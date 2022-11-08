// The constraint system matrix for an arity-2 Merkle tree of 8 leaves using a mocked hasher (one
// selector/gate `s_hash` and one allocation `digest = (l + GAMMA) * (r + GAMMA)` for a random
// gamma and Merkle left/right inputs `l` and `r`).

// |-----||------------------|------------------|----------|---------|-------|---------|--------|--------|
// | row ||       a_col      |       b_col      |  c_col   | pub_col | s_pub | s_bool  | s_swap | s_hash |
// |-----||------------------|------------------|----------|---------|-------|---------|--------|--------|
// |  0  ||       leaf       |      elem_1      |  cbit_1  | cbit_1  |   1   |    1    |    1   |    0   |
// |  1  ||    leaf/elem_1   |   leaf/elem_1    | digest_1 |         |   0   |    0    |    0   |    1   |
// |  2  ||     digest_1*    |      elem_2      |  cbit_2  | cbit_2  |   1   |    1    |    1   |    0   |
// |  3  || digest_1/elem_2  | digest_1/elem_2  | digest_2 |         |   0   |    0    |    0   |    1   |
// |  4  ||     digest_2*    |       elem_3     |  cbit_3  | cbit_3  |   1   |    1    |    1   |    0   |
// |  5  || digest_2/elem_3  | digest_2/elem_3  | digest_3 |  root   |   1   |    0    |    0   |    1   |
// |-----||------------------|------------------|----------|---------|-------|---------|--------|--------|
//   "*" = copy

use halo2_proofs::{
    arithmetic::Field,
    circuit::{Cell, Chip, Layouter, SimpleFloorPlanner, Value},
    pasta::Fp,
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};
use lazy_static::lazy_static;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;

lazy_static! {
    static ref GAMMA: Fp = Fp::random(ChaCha8Rng::from_seed([101u8; 32]));
}

// This serves as a mock hash function because the Poseidon chip has not yet been implemented.
fn mock_hash(a: Fp, b: Fp) -> Fp {
    (a + *GAMMA) * (b + *GAMMA)
}

struct Alloc {
    cell: Cell,
    value: Fp,
}

enum MaybeAlloc {
    Alloc(Alloc),
    Unalloc(Fp),
}

impl MaybeAlloc {
    fn value(&self) -> Fp {
        match self {
            MaybeAlloc::Alloc(alloc) => alloc.value,
            MaybeAlloc::Unalloc(value) => *value,
        }
    }

    fn cell(&self) -> Cell {
        match self {
            MaybeAlloc::Alloc(alloc) => alloc.cell,
            MaybeAlloc::Unalloc(_) => unreachable!(),
        }
    }
}

struct MerkleChip {
    config: MerkleChipConfig,
}

#[derive(Clone, Debug)]
struct MerkleChipConfig {
    a_col: Column<Advice>,
    b_col: Column<Advice>,
    c_col: Column<Advice>,
    s_pub: Selector,
    s_bool: Selector,
    s_swap: Selector,
    s_hash: Selector,
}

impl Chip<Fp> for MerkleChip {
    type Config = MerkleChipConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl MerkleChip {
    fn new(config: MerkleChipConfig) -> Self {
        MerkleChip { config }
    }

    fn configure(cs: &mut ConstraintSystem<Fp>) -> MerkleChipConfig {
        let a_col = cs.advice_column();
        let b_col = cs.advice_column();
        let c_col = cs.advice_column();
        let pub_col = cs.instance_column();

        let s_pub = cs.selector();
        let s_bool = cs.selector();
        let s_swap = cs.selector();
        let s_hash = cs.selector();

        cs.create_gate("public input", |cs| {
            let c = cs.query_advice(c_col, Rotation::cur());
            let pi = cs.query_instance(pub_col, Rotation::cur());
            let s_pub = cs.query_selector(s_pub);
            [s_pub * (c - pi)]
        });

        cs.create_gate("boolean constrain", |cs| {
            let c = cs.query_advice(c_col, Rotation::cur());
            let s_bool = cs.query_selector(s_bool);
            [s_bool * c.clone() * (Expression::Constant(Fp::one()) - c)]
        });

        // |-------|-------|-------|--------|
        // | a_col | b_col | c_col | s_swap |
        // |-------|-------|-------|--------|
        // |   a   |   b   |  bit  |    1   |
        // |   l   |   r   |       |        |
        // |-------|-------|-------|--------|
        // where:
        //     bit = 0  ==>  l = a, r = b
        //     bit = 1  ==>  l = b, r = a
        //
        // Choose left gate:
        //     logic: let l = if bit == 0 { a } else { b }
        //     poly:  bit * (b - a) - (l - a) = 0
        //
        // Choose right gate:
        //     logic: let r = if bit == 0 { b } else { a }
        //     poly:  bit * (b - a) - (b - r) = 0
        //
        // Swap gate = choose left + choose right:
        //     logic: let (l, r) = if bit == 0 { (a, b) } else { (b, a) }
        //     poly: bit * (b - a) - (l - a) + bit * (b - a) - (b - r) = 0
        //           bit * 2 * (b - a)  - (l - a) - (b - r) = 0
        cs.create_gate("swap", |cs| {
            let a = cs.query_advice(a_col, Rotation::cur());
            let b = cs.query_advice(b_col, Rotation::cur());
            let bit = cs.query_advice(c_col, Rotation::cur());
            let s_swap = cs.query_selector(s_swap);
            let l = cs.query_advice(a_col, Rotation::next());
            let r = cs.query_advice(b_col, Rotation::next());
            [s_swap * ((bit * Fp::from(2) * (b.clone() - a.clone()) - (l - a)) - (b - r))]
        });

        // (l + gamma) * (r + gamma) = digest
        cs.create_gate("hash", |cs| {
            let l = cs.query_advice(a_col, Rotation::cur());
            let r = cs.query_advice(b_col, Rotation::cur());
            let digest = cs.query_advice(c_col, Rotation::cur());
            let s_hash = cs.query_selector(s_hash);
            [s_hash
                * ((l + Expression::Constant(*GAMMA)) * (r + Expression::Constant(*GAMMA))
                    - digest)]
        });

        cs.enable_equality(c_col);
        cs.enable_equality(a_col);

        MerkleChipConfig {
            a_col,
            b_col,
            c_col,
            s_pub,
            s_bool,
            s_swap,
            s_hash,
        }
    }

    fn hash_leaf_layer(
        &self,
        layouter: &mut impl Layouter<Fp>,
        leaf: Fp,
        path_elem: Fp,
        c_bit: Fp,
        path_len: usize,
    ) -> Result<Alloc, Error> {
        self.hash_layer_inner(
            layouter,
            MaybeAlloc::Unalloc(leaf),
            path_elem,
            c_bit,
            0,
            path_len,
        )
    }

    fn hash_non_leaf_layer(
        &self,
        layouter: &mut impl Layouter<Fp>,
        prev_digest: Alloc,
        path_elem: Fp,
        c_bit: Fp,
        layer: usize,
        path_len: usize,
    ) -> Result<Alloc, Error> {
        self.hash_layer_inner(
            layouter,
            MaybeAlloc::Alloc(prev_digest),
            path_elem,
            c_bit,
            layer,
            path_len,
        )
    }

    fn hash_layer_inner(
        &self,
        layouter: &mut impl Layouter<Fp>,
        leaf_or_digest: MaybeAlloc,
        path_elem: Fp,
        c_bit: Fp,
        layer: usize,
        path_len: usize,
    ) -> Result<Alloc, Error> {
        let mut digest_alloc: Option<Alloc> = None;

        layouter.assign_region(
            || "leaf layer",
            |mut region| {
                let mut row_offset = 0;

                // Allocate in `a_col` either the leaf or reallocate the previous tree layer's
                // calculated digest (stored in the previous row's `c_col`).
                let a_value = leaf_or_digest.value();

                let a_cell = region
                    .assign_advice(
                        || {
                            format!(
                                "{} (layer {})",
                                if layer == 0 { "leaf" } else { "a" },
                                layer
                            )
                        },
                        self.config.a_col,
                        row_offset,
                        || Value::known(a_value),
                    )?
                    .cell();

                if layer > 0 {
                    let prev_digest_cell = leaf_or_digest.cell();
                    region.constrain_equal(prev_digest_cell, a_cell)?;
                }

                // Allocate private inputs for this tree layer's path element and challenge bit (in
                // columns `b_col` and `c_col` respectively). Expose the challenge bit as a public
                // input.
                let _elem_cell = region.assign_advice(
                    || format!("path elem (layer {})", layer),
                    self.config.b_col,
                    row_offset,
                    || Value::known(path_elem),
                )?;

                let _c_bit_cell = region.assign_advice(
                    || format!("challenge bit (layer {})", layer),
                    self.config.c_col,
                    row_offset,
                    || Value::known(c_bit),
                )?;

                // Expose the challenge bit as a public input.
                self.config.s_pub.enable(&mut region, row_offset)?;

                // Boolean constrain the challenge bit.
                self.config.s_bool.enable(&mut region, row_offset)?;

                // Enable the "swap" gate to ensure the correct order of the Merkle hash inputs.
                self.config.s_swap.enable(&mut region, row_offset)?;

                // In the next row, allocate the correctly ordered Merkle hash inputs, calculated digest, and
                // enable the "hash" gate. If this is the last tree layer, expose the calculated
                // digest as a public input for the tree's root.
                row_offset += 1;

                let (preimg_l_value, preimg_r_value): (Fp, Fp) = if c_bit == Fp::zero() {
                    (a_value, path_elem)
                } else {
                    (path_elem, a_value)
                };

                let _preimg_l_cell = region.assign_advice(
                    || format!("preimg_l (layer {})", layer),
                    self.config.a_col,
                    row_offset,
                    || Value::known(preimg_l_value),
                )?;

                let _preimg_r_cell = region.assign_advice(
                    || format!("preimage right (layer {})", layer),
                    self.config.b_col,
                    row_offset,
                    || Value::known(preimg_r_value),
                )?;

                let digest_value = mock_hash(preimg_l_value, preimg_r_value);

                let digest_cell = region.assign_advice(
                    || format!("digest (layer {})", layer),
                    self.config.c_col,
                    row_offset,
                    || Value::known(digest_value),
                )?;

                digest_alloc = Some(Alloc {
                    cell: digest_cell.cell(),
                    value: digest_value,
                });

                self.config.s_hash.enable(&mut region, row_offset)?;

                // If the calculated digest is the tree's root, expose it as a public input.
                let digest_is_root = layer == path_len - 1;
                if digest_is_root {
                    self.config.s_pub.enable(&mut region, row_offset)?;
                }

                Ok(())
            },
        )?;

        match digest_alloc {
            None => Err(Error::Synthesis),
            Some(inner) => Ok(inner),
        }
    }
}

#[derive(Clone, Default)]
struct MerkleCircuit {
    // Private inputs.
    leaf: Fp,
    path: Vec<Fp>,
    // Public inputs (from the prover). The root is also a public input, but it is calculated within
    // the circuit.
    c_bits: Vec<Fp>,
}

impl Circuit<Fp> for MerkleCircuit {
    type Config = MerkleChipConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn configure(cs: &mut ConstraintSystem<Fp>) -> Self::Config {
        MerkleChip::configure(cs)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fp>,
    ) -> Result<(), Error> {
        let path_len = self.path.len();
        let merkle_chip = MerkleChip::new(config);
        let mut layer_digest = merkle_chip.hash_leaf_layer(
            &mut layouter,
            self.leaf,
            self.path[0],
            self.c_bits[0],
            path_len,
        )?;
        for layer in 1..path_len {
            layer_digest = merkle_chip.hash_non_leaf_layer(
                &mut layouter,
                layer_digest,
                self.path[layer],
                self.c_bits[layer],
                layer,
                path_len,
            )?;
        }
        Ok(())
    }

    fn without_witnesses(&self) -> Self {
        Self::default()
    }
}

#[cfg(test)]
mod tests {
    use super::{mock_hash, MerkleCircuit};
    use halo2_proofs::dev::{FailureLocation, VerifyFailure};
    use halo2_proofs::pasta::Fp;
    use halo2_proofs::plonk::Any;
    use halo2_proofs::{arithmetic::Field, dev::MockProver};
    use rand::{thread_rng, Rng};

    struct Tree(Vec<Vec<Fp>>);

    impl Tree {
        fn rand(n_leaves: usize, tree_layers: usize) -> Self {
            let mut rng = thread_rng();
            let leafs: Vec<Fp> = (0..n_leaves).map(|_| Fp::random(&mut rng)).collect();
            let mut layers = vec![leafs];
            for l in 1..tree_layers {
                let layer: Vec<Fp> = layers[l - 1]
                    .chunks(2)
                    .map(|pair| mock_hash(pair[0], pair[1]))
                    .collect();
                layers.push(layer)
            }
            assert_eq!(layers.last().unwrap().len(), 1);
            Tree(layers)
        }

        fn root(&self) -> Fp {
            self.0.last().unwrap()[0]
        }

        fn leafs(&self) -> &[Fp] {
            self.0.first().unwrap()
        }

        fn gen_path(&self, c: usize, path_len: usize) -> Vec<Fp> {
            let mut path = vec![];
            let mut node_index = c;
            for layer in 0..path_len {
                let sib = if node_index & 1 == 0 {
                    self.0[layer][node_index + 1]
                } else {
                    self.0[layer][node_index - 1]
                };
                path.push(sib);
                node_index /= 2;
            }
            path
        }

        fn calculate_root(leaf: Fp, path: Vec<Fp>, c_bits: Vec<Fp>) -> Fp {
            path.iter()
                .zip(c_bits.iter().map(|x| *x == Fp::one()))
                .fold(leaf, |a, b| {
                    if b.1 {
                        mock_hash(a, *b.0)
                    } else {
                        mock_hash(*b.0, a)
                    }
                })
        }
    }

    struct TestSetup {
        k: u32,
        circuit: MerkleCircuit,
        pub_inputs: Vec<Fp>,
        last_row: usize,
        tree: Tree,
        c: usize,
        c_bits: Vec<Fp>,
    }

    fn setup_test() -> TestSetup {
        // The number of leafs in the Merkle tree. This value can be changed to any power of two.
        let n_leaves: usize = 512;
        let path_len: usize = n_leaves.trailing_zeros() as usize;
        let tree_layers = path_len + 1;

        // The number of rows used in the constraint system matrix (two rows per path element).
        let n_rows_used = 2 * path_len;
        let last_row = n_rows_used - 1;
        assert!(n_leaves.is_power_of_two());

        // Generate a Merkle tree from random data.
        let tree = Tree::rand(n_leaves, tree_layers);

        // Generate a random challenge, i.e. a leaf index in `[0, n_leaves)`.
        let c: usize = thread_rng().gen_range(0..n_leaves);
        let c_bits: Vec<Fp> = (0..path_len).map(|i| Fp::from((c >> i & 1) == 0)).collect();

        // Create the public inputs. Every other row in the constraint system has a public input for a
        // challenge bit, additionally the last row has a public input for the root.
        let k = (n_rows_used as f32).log2().ceil() as u32;
        let mut pub_inputs = vec![tree.root(); 2 * path_len + 1];
        for i in 0..path_len {
            pub_inputs[2 * i] = c_bits[i];
        }
        pub_inputs[last_row] = tree.root();

        // Assert that the constraint system is satisfied for a witness corresponding to `pub_inputs`.
        let circuit = MerkleCircuit {
            leaf: tree.leafs()[c],
            path: tree.gen_path(c, path_len),
            c_bits: c_bits.clone(),
        };
        TestSetup {
            k,
            circuit,
            pub_inputs,
            last_row,
            tree,
            c,
            c_bits,
        }
    }

    // Yucky little method to avoid intermittent test failure - the prover truncates leading 0s but Fp's debug method does not, leading to inconsistencies
    // TODO: find how the prover is truncating the leading 0s - it's surely more elegant than this
    fn format_fp(n: Fp) -> String {
        let mut s = format!("{:?}", n);
        s.remove(0);
        s.remove(0);
        while s.starts_with('0') {
            s.remove(0);
        }
        s.insert_str(0, "0x");
        s
    }

    #[test]
    fn basic_test_works() {
        let s = setup_test();
        let prover = MockProver::run(s.k, &s.circuit, vec![s.pub_inputs]).unwrap();
        assert!(prover.verify().is_ok());
    }

    #[test]
    fn changing_challenge_fails() {
        let s = setup_test();
        let instance_value = s.pub_inputs[0] == Fp::zero();
        let mut bad_pub_inputs = s.pub_inputs;
        bad_pub_inputs[0] = Fp::from(instance_value);

        let prover = MockProver::run(s.k, &s.circuit, vec![bad_pub_inputs]).unwrap();
        assert_eq!(
            prover.verify(),
            Err(vec![VerifyFailure::ConstraintNotSatisfied {
                constraint: ((0, "public input").into(), 0, "").into(),
                location: FailureLocation::InRegion {
                    region: (0, "leaf layer").into(),
                    offset: 0,
                },
                cell_values: vec![
                    (
                        ((Any::Instance, 0).into(), 0).into(),
                        (instance_value as u64).to_string()
                    ),
                    (
                        ((Any::Advice, 2).into(), 0).into(),
                        (!instance_value as u64).to_string()
                    ),
                ],
            }])
        );
    }

    #[test]
    fn changing_root_fails() {
        let s = setup_test();

        // Assert that changing the public root causes the constraint system to become unsatisfied.
        let mut bad_pub_inputs = s.pub_inputs.clone();
        bad_pub_inputs[s.last_row] += Fp::one();
        let last_value = bad_pub_inputs[s.last_row];
        let prover = MockProver::run(s.k, &s.circuit, vec![bad_pub_inputs]).unwrap();
        assert_eq!(
            prover.verify(),
            Err(vec![VerifyFailure::ConstraintNotSatisfied {
                constraint: ((0, "public input").into(), 0, "").into(),
                location: FailureLocation::InRegion {
                    region: (8, "leaf layer").into(),
                    offset: 1,
                },
                cell_values: vec![
                    (((Any::Instance, 0).into(), 0).into(), format_fp(last_value),),
                    (
                        ((Any::Advice, 2).into(), 0).into(),
                        format_fp(s.pub_inputs[s.last_row]),
                    ),
                ],
            }])
        );
    }

    #[test]
    fn non_boolean_challenge_fails() {
        let s = setup_test();
        // Assert that a non-boolean challenge bit causes the boolean constrain and swap gates to fail.
        let mut bad_pub_inputs = s.pub_inputs.clone();
        bad_pub_inputs[0] = Fp::from(2);
        let mut bad_circuit = s.circuit.clone();
        bad_circuit.c_bits[0] = Fp::from(2);
        let prover = MockProver::run(s.k, &bad_circuit, vec![bad_pub_inputs]).unwrap();

        let (first, second) = if s.c & 1 == 0 {
            (s.tree.0[0][s.c], s.tree.0[0][s.c + 1])
        } else {
            (s.tree.0[0][s.c], s.tree.0[0][s.c - 1])
        };

        assert_eq!(
            prover.verify(),
            Err(vec![
                VerifyFailure::ConstraintNotSatisfied {
                    constraint: ((1, "boolean constrain").into(), 0, "").into(),
                    location: FailureLocation::InRegion {
                        region: (0, "leaf layer").into(),
                        offset: 0,
                    },
                    cell_values: vec![(((Any::Advice, 2).into(), 0).into(), "0x2".to_string())],
                },
                VerifyFailure::ConstraintNotSatisfied {
                    constraint: ((2, "swap").into(), 0, "").into(),
                    location: FailureLocation::InRegion {
                        region: (0, "leaf layer").into(),
                        offset: 0,
                    },
                    cell_values: vec![
                        (((Any::Advice, 0).into(), 0).into(), format_fp(first),),
                        (((Any::Advice, 0).into(), 1).into(), format_fp(second),),
                        (((Any::Advice, 1).into(), 0).into(), format_fp(second),),
                        (((Any::Advice, 1).into(), 1).into(), format_fp(first)),
                        (((Any::Advice, 2).into(), 0).into(), "0x2".to_string(),),
                    ],
                }
            ])
        );
    }

    #[test]
    fn changing_path_fails() {
        let s = setup_test();
        // Assert that changing the witnessed path causes the constraint system to become unsatisfied
        // when checking that the calculated root is equal to the public input root.
        let mut bad_circuit = s.circuit;
        bad_circuit.path[0] += Fp::one();
        let bad_root =
            Tree::calculate_root(bad_circuit.clone().leaf, bad_circuit.clone().path, s.c_bits);

        let prover = MockProver::run(s.k, &bad_circuit, vec![s.pub_inputs.clone()]).unwrap();
        assert_eq!(
            prover.verify(),
            Err(vec![VerifyFailure::ConstraintNotSatisfied {
                constraint: ((0, "public input").into(), 0, "").into(),
                location: FailureLocation::InRegion {
                    region: (8, "leaf layer").into(),
                    offset: 1,
                },
                cell_values: vec![
                    (
                        ((Any::Instance, 0).into(), 0).into(),
                        format_fp(s.pub_inputs[s.last_row])
                    ),
                    (((Any::Advice, 2).into(), 0).into(), format_fp(bad_root),),
                ],
            }])
        );
    }
}
