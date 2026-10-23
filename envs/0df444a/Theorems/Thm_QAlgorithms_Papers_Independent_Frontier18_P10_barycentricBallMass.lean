-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P10_barycentricBallMass
-- name    : QAlgorithms.Papers.Independent.Frontier18.P10.barycentricBallMass
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:09:47.396465+00:00
-- url     : https://prove2.me/theorems/5cd1cd2e-22d6-4930-81f8-7a4ae1859c5a
-- title:
--   Lemma 2: barycentric mass near the unit sphere
-- statement:
--   Let $H$ be a complete separable real Hilbert space, $B=\{y:\|y\|\le1\}$, $\delta>0$, and $z\in B$ with $\|z\|>1-\delta$. For every Borel probability $\mu$ on $B$ with Pettis barycenter $z$,
--   $$\mu\{y\in B:\|y-z\|\le\delta\}\ge
--   \frac{\delta^2-(1-\|z\|^2)}{\delta^2-(1-\|z\|)^2}.$$
--   The denominator is positive under these assumptions.
--
--   The estimate also includes $z=0$ when the hypotheses allow it.
-- source:
--   Generalized compactness in linear spaces and its applications, arXiv:1002.3610v3, PDF p. 9, Lemma 2: barycentric mass near the unit sphere

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P10

noncomputable section

open Set Filter MeasureTheory TopologicalSpace

open scoped Topology ENNReal BigOperators

universe u v w

namespace QAlgorithms.Papers.Independent.Frontier18.P10

open QAlgorithms.Papers.Independent.Dependency50.P25

attribute [local instance] QAlgorithms.Papers.Independent.Frontier18.P10.paperMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Frontier18.P10.paperBorel

section HilbertResults

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [hcomplete : CompleteSpace H]

include hcomplete

/-- Lemma 2, PDF p.9: the closed radius-delta ball has this barycentric mass
lower bound. No nonzero-z hypothesis is added. -/
theorem barycentricBallMass [SeparableSpace H]
    (delta : ℝ) (hdelta : 0 < delta) (z : H) (hz : ‖z‖ ≤ 1)
    (hnear : 1 - delta < ‖z‖)
    (mu : ProbabilityMeasure (Metric.closedBall (0 : H) 1))
    (hb : pettisBarycenter (Metric.closedBall (0 : H) 1) mu = z) :
    (delta ^ 2 - (1 - ‖z‖ ^ 2)) / (delta ^ 2 - (1 - ‖z‖) ^ 2) ≤
      ((mu : Measure (Metric.closedBall (0 : H) 1))
        {y | ‖(y : H) - z‖ ≤ delta}).toReal := by sorry

end HilbertResults

end QAlgorithms.Papers.Independent.Frontier18.P10

end
