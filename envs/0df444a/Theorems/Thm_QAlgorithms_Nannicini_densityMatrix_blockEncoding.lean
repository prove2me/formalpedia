-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_densityMatrix_blockEncoding
-- name    : QAlgorithms.Nannicini.densityMatrix_blockEncoding
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:52:19.287105+00:00
-- url     : https://prove2.me/theorems/4addcb18-b223-46a6-8837-38a9df8f8190
-- title:
--   Block-encoding a density matrix from a unitary preparing its purification
-- statement:
--   Let $q, a \in \mathbb{N}$. There is a quantum circuit $\mathcal{C}$ on $(q+a) + q$ qubits, fixed independently of the unitary below, that calls an oracle $U$ at most once, its inverse $U^\dagger$ at most once (both uncontrolled), and otherwise uses at most $q + 1$ two-qubit gates, with the following property. Let $U$ be any $(q+a)$-qubit unitary and $\rho$ any $q$-qubit density matrix such that $|\varrho\rangle = U|0\rangle_q|0\rangle_a$ is a purification of $\rho$, i.e.
--
--   $$
--   \operatorname{Tr}_a\bigl(|\varrho\rangle\langle\varrho|\bigr) = \rho .
--   $$
--
--   Then the unitary $\mathcal{C}(U)$ of the circuit is a $(1, q+a, 0)$-block-encoding of $\rho$:
--
--   $$
--   \bigl(\langle 0|_{q+a} \otimes I\bigr)\, \mathcal{C}(U)\, \bigl(|0\rangle_{q+a} \otimes I\bigr) = \rho ,
--   $$
--
--   where the auxiliary register consists of the first $q + a$ qubits.
--
--   This lets algorithms that can only prepare a state treat its density matrix as a block-encoded operator, e.g. for trace estimation and Gibbs-sampling based SDP solvers.
--
--   **Formalization Note** The source says the density matrix may be subnormalized (Def. 7.35). In the stated resources that case cannot hold, so the statement is given for a normalized density matrix with a purification in the sense of Def. 1.69; the discrepancy is recorded in the theorem's docstring and in HARD.md. The circuit is quantified before $U$ and $\rho$, so it depends only on $q$ and $a$.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 172, Lemma 7.39. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_Adiabatic
import Definitions.Def_QAlgorithms_Nannicini_Ch07b_Model
set_option autoImplicit false

namespace QAlgorithms.Nannicini


/-- Nannicini p.172, Lemma 7.39 (Lem. 6.4.4 in [Gilyén, 2019]), stated for a normalized density
matrix. Let `U` be a `(q + a)`-qubit unitary such that `U|0⟩_q|0⟩_a = |ϱ⟩` is a purification of the
`q`-qubit density matrix `ρ` (Def. 1.69, p.40: tracing out the last `a` qubits of `|ϱ⟩⟨ϱ|` gives
`ρ`). Then there is a circuit, fixed before `U` and `ρ`, using `U` once, `U†` once (uncontrolled)
and at most `q + 1` two-qubit gates on `(q + a) + q` wires, whose unitary is a
`(1, q + a, 0)`-block-encoding of `ρ` (auxiliary register = the first `q + a` wires).

Discrepancy with the page (trap 30): the source allows a subnormalized `ρ` (Def. 7.35). In that
case the claim fails in the stated resources: with the auxiliary register of `q + a` qubits
starting and ending in `|0⟩`, the block entries of any such circuit are `⟨ϱ, x|S|ϱ, y⟩` for a
unitary `S`, and equating them with the `|0⟩_B`-block of the partial trace for every `U` forces
`S` to vanish on the `|1⟩_B` branch. The normalized case is the one the construction
`(U† ⊗ I)(SWAP ⊗ I)(U ⊗ I)` proves. -/
theorem densityMatrix_blockEncoding (q a : ℕ) :
    ∃ c : OracleCircuit twoQubitGateSet (fun _ : Fin 1 => q + a) ((q + a) + q),
      (c.countP fun s => match s with
        | OracleStep.query _ false _ _ _ => true
        | _ => false) ≤ 1 ∧
      (c.countP fun s => match s with
        | OracleStep.query _ true _ _ _ => true
        | _ => false) ≤ 1 ∧
      (∀ s ∈ c, match s with
        | OracleStep.query _ _ ctrl _ _ => ctrl = none
        | OracleStep.gate _ => True) ∧
      c.gateCount ≤ q + 1 ∧
      ∀ (U : Matrix (Qubits (q + a)) (Qubits (q + a)) ℂ) (ρ : Matrix (Qubits q) (Qubits q) ℂ),
        U ∈ Matrix.unitaryGroup (Qubits (q + a)) ℂ → IsDensityMatrix ρ →
        traceRight (pureDensity (WithLp.toLp 2 fun p : Qubits q × Qubits a =>
          act U (zeroKet (q + a)) ((qubitsAppendEquiv q a).symm p))) = ρ →
        IsBlockEncoding (0 : Qubits (q + a))
          ((c.unitary fun _ => U).submatrix (qubitsAppendEquiv (q + a) q).symm
            (qubitsAppendEquiv (q + a) q).symm) 1 0 ρ := by
  sorry











end QAlgorithms.Nannicini
