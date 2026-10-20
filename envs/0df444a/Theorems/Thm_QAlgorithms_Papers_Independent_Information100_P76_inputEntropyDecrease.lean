-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P76_inputEntropyDecrease
-- name    : QAlgorithms.Papers.Independent.Information100.P76.inputEntropyDecrease
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:02:11.010732+00:00
-- url     : https://prove2.me/theorems/acb921b2-a604-4f47-86d4-92a7129acc3a
-- title:
--   Proposition 7.4: input-only entropy-decrease lower bound
-- statement:
--   For a CPTP map $\Phi:M_q(\mathbb C)\to M_q(\mathbb C)$ with $q\ge1$, the normalized input state space has an entropy-decrease maximizer, and
--
--   $$\kappa(\Phi)\ge\max_\rho\bigl[S(\rho)-S(\Phi(\rho))\bigr].$$
--
--   Entropy is measured in bits, and $\kappa$ uses the ordered positive-error and full-rank-input optimization of Definition 1.3. The maximum here is over all input density matrices, including singular ones. This is a lower bound involving only the fixed-dimensional input space, rather than an equality or an unrestricted auxiliary optimization.
-- source:
--   Bath dimension and initial entropy for closed repeated use of a quantum channel, arXiv:2609.18267v1, PDF p. 12, Proposition 7.4

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P76

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P76

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open Filter

/-- PDF pp.12–13, Proposition 7.4: the entropy-decrease maximum is attained on the
finite input state space; it is a lower bound, not a formula for the intrinsic cost. -/
theorem inputEntropyDecrease {q : ℕ} (hq : 0 < q)
    (Phi : Superop (Fin q) (Fin q)) (hPhi : IsChannel Phi) :
    ∃ rho : Op q, IsDensityMatrix rho ∧
      (∀ sigma : Op q, IsDensityMatrix sigma →
        vnEntropy sigma - vnEntropy (Phi sigma) ≤ vnEntropy rho - vnEntropy (Phi rho)) ∧
      vnEntropy rho - vnEntropy (Phi rho) ≤ intrinsicCost Phi := by sorry

end QAlgorithms.Papers.Independent.Information100.P76

end
