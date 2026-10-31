-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_reverse_samson_sharp
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.reverse_samson_sharp
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:32:27.137625+00:00
-- url     : https://prove2.me/theorems/7a06d7c0-4e4e-4a0e-a403-dfe755c7b7a0
-- title:
--   Theorem 8: Inf [d2sq(P,Q)+d2sq(Q,P)]/D(P||Q)=min{kappa(beta1^{-1}),kappa(beta2)}, where kappa=(t-1)^2/[r(t)max(1,t)]
-- statement:
--   Fix $\beta_1,\beta_2\in(0,1)$. Over all probability pairs whose two essential density bounds are exactly these betas,
--
--   $$\inf\frac{d_2^2(P,Q)+d_2^2(Q,P)}{D(P\|Q)}
--   =\min\{\kappa(\beta_1^{-1}),\kappa(\beta_2)\},\qquad
--   \kappa(t)=\frac{(t-1)^2}{r(t)\max\{1,t\}}.$$
--
--   The formal statement characterizes the greatest universal lower coefficient. Exact betas imply mutual absolute continuity and positive finite denominator; sharpness is retained.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 26, Theorem 8

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Theorem 8: Inf [d2sq(P,Q)+d2sq(Q,P)]/D(P||Q)=min{kappa(beta1^{-1}),kappa(beta2)}, where kappa=(t-1)^2/[r(t)max(1,t)]. Sason--Verdu, arXiv:1508.00335v7, PDF p.26.  -/
theorem reverse_samson_sharp
    (b : LogBase) (b1 b2 : ℝ) (h1 : 0 < b1 ∧ b1 < 1) (h2 : 0 < b2 ∧ b2 < 1) :
    IsGreatest {c : ℝ≥0∞ | ∀ (A : Type u) [MeasurableSpace A] (P Q : Measure A)
      [IsProbabilityMeasure P] [IsProbabilityMeasure Q], exactPairs b1 b2 P Q →
        c * kl b P Q ≤ martonSum P Q}
      (ENNReal.ofReal (min (samsonKernel b b1⁻¹) (samsonKernel b b2))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
