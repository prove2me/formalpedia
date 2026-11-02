-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P21_fixed_fidelity_minimum
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P21.fixed_fidelity_minimum
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:58:58.893119+00:00
-- url     : https://prove2.me/theorems/0a17cc0e-5d31-4a06-862e-86d65e321737
-- title:
--   Exact constrained Schmidt minimum and an attaining probability vector
-- statement:
--   Let $d\ge2$ and $F\in[1/d,1]$. Consider all $d$ nonnegative Schmidt probabilities $\mu_k$ summing to one with $\sum_k\sqrt{\mu_k}=\sqrt{dF}$. Define
--
--   $$
--   \gamma=\sqrt{F/d}+\sqrt{(d-1)(1-F)/d},\qquad
--   \delta=\sqrt{F/d}-\sqrt{(1-F)/(d(d-1))}.
--   $$
--
--   The constrained pure-tangle minimum is
--
--   $$
--   q_d(F)=\min_{\mu}\,2\Bigl(1-\sum_k\mu_k^2\Bigr)
--   =2\bigl(1-\gamma^4-(d-1)\delta^4\bigr).
--   $$
--
--   It is attained by the feasible vector $(\gamma^2,\delta^2,\ldots,\delta^2)$. Zero probabilities at $F=1/d$ and uniform probabilities at $F=1$ are included.
--
--   This gives the exact raw profile whose convex envelope yields isotropic tangle.
-- source:
--   I-concurrence and tangle for isotropic states, arXiv:quant-ph/0208002v1, PDF p. 9, §3.3, (3.30)–(3.32): exact constrained Schmidt minimum

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P21

open scoped Matrix ComplexConjugate

open Filter

open QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P03
  (PureEnsemble convexRoof pureConcurrence concurrence SchmidtData schmidtVector)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.8--9, (3.30)--(3.32): exact attained constrained Schmidt minimum,
including zero Schmidt probabilities at F=1/d and the equal endpoint F=1. -/
theorem fixed_fidelity_minimum (d : ℕ) (hd : 2 ≤ d) (F : ℝ)
    (hF : F ∈ Set.Icc (1 / (d : ℝ)) 1) :
    constrainedSchmidtTangle d F = explicitQ d F ∧
    IsLeast (profileValues d F) (explicitQ d F) ∧
    (∃ mu : SchmidtProbabilities d,
      mu.probability = minimizingProbabilities d F ∧
      (∑ k, Real.sqrt (mu.probability k)) = Real.sqrt ((d : ℝ) * F) ∧
      schmidtCost mu.probability = explicitQ d F) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P21

end
