-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_js_hellinger_bounds
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.js_hellinger_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:34:01.840532+00:00
-- url     : https://prove2.me/theorems/5c3ce523-6be5-4e0b-b1f2-74989ed35815
-- title:
--   Theorem 11: For alpha<1, JS/H_alpha lies between the minimum of its two endpoint kernel values and the maximum over the whole closed density interval; for alpha>1 it lies between the upper-density and
-- statement:
--   For $P\ll Q$, $P\ne Q$, define the continuous kernel $\kappa_\alpha$ by (195): off endpoints it equals $(\alpha-1)[t\log_b t-(t+1)\log_b((t+1)/2)]/(t^\alpha+\alpha-1-\alpha t)$; its values at 0,1,infinity are $\log_b2$, $(\log_b e)/(2\alpha)$, and $(1/\alpha-1)^+\log_b2$. For $0<\alpha<1$,
--
--   $$\min\{\kappa_\alpha(\beta_1^{-1}),\kappa_\alpha(\beta_2)\}H_\alpha
--   \le JS\le\max_{t\in[\beta_2,\beta_1^{-1}]}\kappa_\alpha(t)H_\alpha.$$
--
--   For $\alpha>1$, the lower coefficient is $\kappa_\alpha(\beta_1^{-1})$ and the upper is $\kappa_\alpha(\beta_2)$. The maximum for $\alpha<1$ ranges over the whole closed interval. Its supremum expression has the same value by continuity on this compact extended interval.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 29, Theorem 11

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Theorem 11: For alpha<1, JS/H_alpha lies between the minimum of its two endpoint kernel values and the maximum over the whole closed rnDensityReal interval; for alpha>1 it lies between the upper-rnDensityReal and lower-rnDensityReal endpoint values. Sason--Verdu, arXiv:1508.00335v7, PDF p.29.  -/
theorem js_hellinger_bounds
    (b : LogBase) (a : ℝ) (ha : 0 < a ∧ a ≠ 1)
    {A : Type u} [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hPQ : P ≪ Q) (hne : P ≠ Q) :
    (a < 1 → min (jsHellingerKernel b a (upperDensity P Q))
      (jsHellingerKernel b a (ENNReal.ofReal (inverseUpperDensity Q P))) * hellinger a P Q ≤ js b P Q ∧
      js b P Q ≤ (⨆ t : Icc (ENNReal.ofReal (inverseUpperDensity Q P)) (upperDensity P Q),
        jsHellingerKernel b a t) * hellinger a P Q) ∧
    (1 < a → jsHellingerKernel b a (upperDensity P Q) * hellinger a P Q ≤ js b P Q ∧
      js b P Q ≤ jsHellingerKernel b a (ENNReal.ofReal (inverseUpperDensity Q P)) * hellinger a P Q) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
