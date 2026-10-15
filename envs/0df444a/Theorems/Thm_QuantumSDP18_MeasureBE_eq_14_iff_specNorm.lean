-- Prove2me | Theorems.Thm_QuantumSDP18_MeasureBE_eq_14_iff_specNorm
-- name    : QuantumSDP18.MeasureBE.eq_14_iff_specNorm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:30:30.261716+00:00
-- url     : https://prove2.me/theorems/53c4bfbc-00cf-4d8d-8c47-40af3fa3573e
-- title:
--   §4.1, p. 25 — ∀ρ: |Tr([K − M]ρ)| ≤ ε ⟺ ‖K − M‖ ≤ ε, ρ over density matrices, M Hermitian
-- statement:
--   Let $U$ be an operator on the system and $a$ ancilla qubits, let $K = (I\otimes\langle 0|^{\otimes a})\,U^\dagger(I\otimes|0\rangle\langle 0|)U\,(I\otimes|0\rangle^{\otimes a})$ be its block, let $M$ be a Hermitian operator on the system, and let $\varepsilon \ge 0$. Then
--
--   $$
--   \forall\rho:\ \Big|\operatorname{Tr}\big([K - M]\rho\big)\Big| \le \varepsilon
--   \quad\Longleftrightarrow\quad \|K - M\| \le \varepsilon,
--   $$
--
--   where $\rho$ ranges over all density matrices on the system (positive semidefinite, trace one) and $\|\cdot\|$ is the operator norm.
--
--   Together with the trace identity, this turns the statement that the measurement is implemented with bias at most $\varepsilon$ (equation (14)) into an operator-norm bound on $K - M$, which is the form a block-encoding requires.
--
--   **Formalization Note** The page applies this to a POVM element $M$; only its Hermiticity is used, and that is the hypothesis here. $\varepsilon \ge 0$ (a bias is nonnegative) matters only when the system is zero-dimensional, where the left side holds vacuously. The absolute value is the modulus of the complex trace. The operator norm is the platform's `QAlgorithms.specNorm`. $U$ need not be unitary.
-- source:
--   van Apeldoorn and Gilyén, Improvements in quantum SDP-solving with applications, arXiv:1804.05058v1, p. 25, §4.1, 'Therefore (14) is equivalent to saying that' and the display that follows

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BlockEncoding
import Definitions.Def_QuantumSDP18_MeasureBE_Setting

namespace QuantumSDP18.MeasureBE

/-- §4.1, p. 25: (14) is equivalent to
`∀ρ: |Tr([K − M] ρ)| ≤ ε ⟺ ‖K − M‖ ≤ ε`, where `K = (I ⊗ ⟨0|^{⊗a}) U† (I ⊗ |0⟩⟨0|) U (I ⊗ |0⟩^{⊗a})`,
`ρ` ranges over density matrices and `‖·‖` is the operator norm. `M` is Hermitian (a POVM
element); `ε ≥ 0` (a bias). -/
theorem eq_14_iff_specNorm {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ℕ)
    (U : Matrix (ι × Anc c) (ι × Anc c) ℂ) (M : Matrix ι ι ℂ) (ε : ℝ)
    (hM : M.IsHermitian) (hε : 0 ≤ ε) :
    (∀ ρ : Matrix ι ι ℂ, IsDensity ρ → ‖((blockK c U - M) * ρ).trace‖ ≤ ε) ↔
      QAlgorithms.specNorm (blockK c U - M) ≤ ε := by sorry

end QuantumSDP18.MeasureBE
