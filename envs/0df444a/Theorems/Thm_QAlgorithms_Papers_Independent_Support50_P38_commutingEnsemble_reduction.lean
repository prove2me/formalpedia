-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P38_commutingEnsemble_reduction
-- name    : QAlgorithms.Papers.Independent.Support50.P38.commutingEnsemble_reduction
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T22:08:06.632532+00:00
-- url     : https://prove2.me/theorems/4c7abafb-5b84-440e-b779-1165667bc0b4
-- title:
--   Common eigenbasis and classical total variation
-- statement:
--   Let $X$ be finite nonempty, and let $\rho_x$ be pairwise commuting positive semidefinite trace-one matrices on the same finite nonzero-dimensional complex Hilbert space $Y$. There is a unitary $U$ and a normalized probability law $W_x$ on a common basis for each $x$ such that
--
--   $$
--   \rho_x=U\operatorname{diag}(W_x)U^*,\qquad
--   \frac12\left\|U\operatorname{diag}(p)U^*-U\operatorname{diag}(q)U^*\right\|_1
--    =d_{\rm TV}(p,q)
--   $$
--   for any two probability laws $p,q$ on that basis. The norm is the trace norm. This identifies classical source states and their fidelity criterion inside the quantum model; it does not eliminate arbitrary quantum intermediate encodings or equate optimized costs.
-- source:
--   Compression of sources of probability distributions and density operators, arXiv:quant-ph/0208131v1, PDF p. 10, Section VII, paragraph after (17)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P38

open scoped BigOperators Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon labelInformation)

attribute [local instance] Classical.propDecidable

/-- PDF p.10: a commuting density ensemble has a common eigenbasis and classical
probability laws; half trace norm in that basis equals total variation. No equality of
optimal classical and arbitrary-quantum-intermediate code costs is asserted. -/
theorem commutingEnsemble_reduction {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : A → Matrix B B ℂ) (hrho : ∀ a, QAlgorithms.IsDensityMatrix (rho a))
    (hcomm : ∀ a b, Commute (rho a) (rho b)) :
    ∃ (u : Matrix B B ℂ) (w : A → B → ℝ),
      uᴴ * u = 1 ∧ u * uᴴ = 1 ∧ IsStochastic w ∧
      (∀ a, rho a = diagonalIn u (w a)) ∧
      (∀ p q : B → ℝ, IsLaw p → IsLaw q →
        QAlgorithms.traceNorm (diagonalIn u p - diagonalIn u q) / 2 = tv p q) := by sorry

end QAlgorithms.Papers.Independent.Support50.P38

end
