-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_sparse_blockEncoding
-- name    : QAlgorithms.Nannicini.sparse_blockEncoding
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:52:10.856417+00:00
-- url     : https://prove2.me/theorems/ac2afd36-e628-4ba6-a7e9-b1c1ddd7ee50
-- title:
--   Block-encoding from sparse-access oracles (rotation cost and entry encoding made explicit)
-- statement:
--   Let $A \in \mathbb{C}^{2^q\times 2^q}$ have at most $s_r$ nonzero entries in each row and at most $s_c$ in each column, with $|a_{ij}|\le 1$ for all $i,j$, and $s_r, s_c \le 2^q$. For a row $i$ and $k < s_r$ let $r_{ik}$ be the column of the $k$-th nonzero entry of row $i$ (zero-based, increasing order), or $k + 2^q$ if row $i$ has at most $k$ nonzero entries. Define $c_{\ell j}$ in the same way for columns, with $\ell < s_c$. Indices are held in $(q+1)$-qubit registers, most significant bit first.
--
--   The access model consists of three unitaries:
--
--   1. $O_r : |i\rangle|k\rangle \mapsto |i\rangle|r_{ik}\rangle$ for $i < 2^q$ and $k < s_r$, acting on two $(q+1)$-qubit registers;
--   2. $O_c : |\ell\rangle|j\rangle \mapsto |c_{\ell j}\rangle|j\rangle$ for $\ell < s_c$ and $j < 2^q$, acting on the same kind of registers;
--   3. $O_A : |i\rangle|j\rangle|0\rangle_p \mapsto |i\rangle|j\rangle|z_{ij}\rangle$ for $i,j < 2^q$ ($q$-qubit index registers), where $z_{ij}\in\{0,1\}^p$ is a code of $a_{ij}$ under a fixed decoding map $\mathrm{dec}:\{0,1\}^p\to\mathbb{C}$, that is, $\mathrm{dec}(z_{ij}) = a_{ij}$.
--
--   Let $R$ be a circuit of one- and two-qubit gates on $1+p+w$ qubits that performs the final rotation to accuracy $\eta$: for every $z$ with $|\mathrm{dec}(z)|\le 1$,
--
--   $$
--   \bigl|\langle 0, z, 0_w|\,R\,|0, z, 0_w\rangle - \mathrm{dec}(z)\bigr| \le \eta .
--   $$
--
--   There are absolute constants $C, c$ such that, for all $q, s_r, s_c, p, \mathrm{dec}, w, R, \eta$ as above, some circuit of one- and two-qubit gates, chosen independently of $A$ and of the oracles, acts on $q+3$ auxiliary qubits, $m \le C(p+w+1)$ workspace qubits and the $q$ system qubits, and has the following properties. It queries $O_r$ once and $O_c$ once (each possibly as its adjoint), and $O_A$ and $O_A^\dagger$ once each, all uncontrolled. It uses at most
--
--   $$
--   C\,(q+1)\,\log_2(q+2)^{c} + |R|
--   $$
--
--   further gates. For every such $A$ and every oracles $O_r, O_c, O_A$ as above, with the auxiliary and workspace qubits in $|0\rangle$, it is a
--
--   $$
--   \bigl(\sqrt{s_r s_c},\; q+3,\; \sqrt{s_r s_c}\,\eta\bigr)\text{-block-encoding of } A .
--   $$
--
--   This converts the classical sparse-access description of a matrix into a block-encoding, which is the usual entry point of block-encoding algorithms for sparse matrices.
--
--   **Correction.** The source claims $\tilde O(q)$ gates and $\tilde O(p)$ auxiliary qubits with an unspecified error $\xi$. It never fixes the $p$-bit encoding of a complex entry. It also does not count the arithmetic of the final rotation $|0\rangle\mapsto a|0\rangle+\sqrt{1-|a|^2}|1\rangle$, which it defers to Berry et al. (2015) and whose cost grows with $p$ and with $\log(1/\xi)$. Here the encoding is an arbitrary decoding map, the rotation is an explicit circuit $R$ whose size is added to the gate count, and the error is $\xi = \sqrt{s_r s_c}\,\eta$ (Remark 7.22: the error comes from the final rotation only).
--
--   **Formalization Note** The circuit is an oracle circuit over the gate set of all one- and two-qubit unitaries. The register index is reordered as (auxiliary, workspace, system), and the system basis state $|i\rangle$ is the integer $i$. $\tilde O(q)$ is rendered as $C(q+1)\log_2(q+2)^c$, with $C$ and $c$ quantified before every other object. The circuit is quantified before $A$ and the oracles, so $A$ enters only through the queries.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 164, Proposition 7.21. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_BlockEncoding
import Definitions.Def_QAlgorithms_Nannicini_Ch07a_Model
set_option autoImplicit false

namespace QAlgorithms.Nannicini















/-- Corrected statement. Nannicini Proposition 7.21 (p.164), block-encoding from sparse-access
oracles.

**Printed claim.** For `A ∈ ℂ^{2^q×2^q}` with at most `s_r` nonzeros per row, at most `s_c` per
column and `|a_ij| ≤ 1`, given `O_r : |i⟩|k⟩ ↦ |i⟩|r_ik⟩`, `O_c : |ℓ⟩|j⟩ ↦ |c_ℓj⟩|j⟩` and
`O_A : |i⟩|j⟩|0⟩_p ↦ |i⟩|j⟩|a_ij⟩` (`a_ij` a `p`-digit binary description), one can implement a
`(√(s_r s_c), q + 3, ξ)`-block-encoding of `A` with a single use of `O_r, O_c, O_A, O_A†`,
additionally using `Õ(q)` one- and two-qubit gates and `Õ(p)` auxiliary qubits.

**What is changed.** (1) The `p`-digit description is an arbitrary decoding map
`dec : {0,1}^p → ℂ` (universally quantified): `O_A` writes a code `z` with `dec z = a_ij`.
(2) The final rotation `|0⟩ ↦ a|0⟩ + √(1 − |a|²)|1⟩` computed from `z` (deferred by the source to
[Berry et al., 2015]) is an explicit given circuit `R` of one- and two-qubit gates on
`1 + p + w` qubits whose `⟨0, z, 0_w|R|0, z, 0_w⟩` amplitude is within `η` of `dec z` (whenever
`|dec z| ≤ 1`). The gate count is `Õ(q)` **plus the size of `R`**, the extra qubits are
`O(p + w)`, and the error is `ξ = √(s_r s_c)·η` (Rem. 7.22: ξ comes from the final rotation
only; `η = 0` gives an exact block-encoding).

**Why.** The printed claim cannot be stated as is: the encoding of a complex entry in `p` bits
is never specified, the rotation computed from a `p`-bit description costs gates growing
polynomially in `p` (or in `log(1/ξ)`), which `Õ(q)` does not absorb, and `ξ` is left free with
no stated dependence of the cost on it.

**Reading of the rest.** Wires: `(q + 3)` auxiliary qubits, `m` workspace qubits, `q` system
qubits; the block-encoding has the auxiliary and the workspace qubits in `|0⟩` (the workspace is
returned clean, the meaning of "additionally using auxiliary qubits"). The system basis state
`|i⟩` is the integer `i` (most significant bit first). `O_r`, `O_c` are specified, as on p.164,
only on `i, j < 2^q`, `k < s_r`, `ℓ < s_c` (indices held in `q + 1` qubits); `O_A` on
`i, j < 2^q` with the value register `|0⟩_p`. `s_r, s_c ≤ 2^q` is the source's implicit
convention (`k + 2^q` must fit in `q + 1` qubits). "A single use" of `O_r` (resp. `O_c`) is one
uncontrolled query, possibly the adjoint (the proof uses `O_r†` through `U_L†`); `O_A` and
`O_A†` are used once each, uncontrolled. `Õ(q)` is `C (q + 1) log₂(q + 2)^c` with absolute
`C, c`. The circuit is chosen from `q, s_r, s_c, p, dec, w, R, η` only, before `A` and the
oracles (trap Q2): `A` enters only through the oracle queries. -/
theorem sparse_blockEncoding :
    ∃ C c : ℕ, ∀ (q sr sc : ℕ), sr ≤ 2 ^ q → sc ≤ 2 ^ q →
      ∀ (p : ℕ) (dec : Qubits p → ℂ) (w : ℕ) (R : Circuit oneTwoQubitGateSet (1 + p + w)) (η : ℝ),
      (∀ z : Qubits p, ‖dec z‖ ≤ 1 →
        ‖R.unitary (Fin.append (Fin.append (fun _ => false) z) fun _ => false)
            (Fin.append (Fin.append (fun _ => false) z) fun _ => false) - dec z‖ ≤ η) →
      ∃ (m : ℕ) (circ : OracleCircuit oneTwoQubitGateSet (sparseOracleArity q p) ((q + 3 + m) + q)),
        m ≤ C * (p + w + 1) ∧
        circ.queryCount 0 = 1 ∧ circ.queryCount 1 = 1 ∧
        circ.countP (OracleStep.IsUseOf 2 false) = 1 ∧
        circ.countP (OracleStep.IsUseOf 2 true) = 1 ∧
        (∀ s ∈ circ, OracleStep.IsControlledQuery s = false) ∧
        circ.gateCount ≤ C * (q + 1) * Nat.log 2 (q + 2) ^ c + R.size ∧
      ∀ (A : Matrix (Fin (2 ^ q)) (Fin (2 ^ q)) ℂ),
      (∀ i, (sparseRowSupport A i).card ≤ sr) → (∀ j, (sparseColSupport A j).card ≤ sc) →
      (∀ i j, ‖A i j‖ ≤ 1) →
      ∀ (Or Oc : Matrix (Qubits ((q + 1) + (q + 1))) (Qubits ((q + 1) + (q + 1))) ℂ)
        (OA : Matrix (Qubits (q + q + p)) (Qubits (q + q + p)) ℂ),
      Or ∈ Matrix.unitaryGroup _ ℂ → Oc ∈ Matrix.unitaryGroup _ ℂ → OA ∈ Matrix.unitaryGroup _ ℂ →
      (∀ (i : Fin (2 ^ q)) (k : ℕ), k < sr →
        act Or (ket (Fin.append (natToBits (q + 1) i) (natToBits (q + 1) k))) =
          ket (Fin.append (natToBits (q + 1) i) (natToBits (q + 1) (sparseRowIndex A i k)))) →
      (∀ (l : ℕ) (j : Fin (2 ^ q)), l < sc →
        act Oc (ket (Fin.append (natToBits (q + 1) l) (natToBits (q + 1) j))) =
          ket (Fin.append (natToBits (q + 1) (sparseColIndex A j l)) (natToBits (q + 1) j))) →
      (∃ code : Fin (2 ^ q) → Fin (2 ^ q) → Qubits p, (∀ i j, dec (code i j) = A i j) ∧
        ∀ i j : Fin (2 ^ q),
          act OA (ket (Fin.append (Fin.append (natToBits q i) (natToBits q j)) fun _ => false)) =
            ket (Fin.append (Fin.append (natToBits q i) (natToBits q j)) (code i j))) →
        IsBlockEncoding (((fun _ => false), (fun _ => false)) : Qubits (q + 3) × Qubits m)
          (Matrix.reindex (sparseBERegEquiv q m) (sparseBERegEquiv q m)
            (circ.unitary (sparseOracles Or Oc OA)))
          (Real.sqrt ((sr : ℝ) * sc)) (Real.sqrt ((sr : ℝ) * sc) * η)
          (A.submatrix (bitsEquivFin q) (bitsEquivFin q)) := by
  sorry

end QAlgorithms.Nannicini
