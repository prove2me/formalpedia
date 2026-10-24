-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P15_remark9
-- name    : QAlgorithms.Papers.Independent.Support50.P15.remark9
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:41:29.551446+00:00
-- url     : https://prove2.me/theorems/736ab79e-752d-477f-aa99-3d4100326b37
-- title:
--   remark9
-- statement:
--   For every integer $d\ge2$, put $N_d=\tfrac14\log^2(d-1)+1$ and let $N(d)$ be Eq. (7). Then
--
--   $$N_d-1<N(d)<N_d.$$
--
--   Its optimizing parameter $r_d$ is the unique root in $(0,1/2)$ of $(1-2r)\log(((1-r)/r)(d-1))=2$. There are $C>0$ and an integer $d_0\ge3$ such that, for all $d\ge d_0$,
--
--   $$0\le N_d-N(d)\le\frac C{\log^2d},\qquad\left|r_d-\left(\frac12-\frac1{\log(d-1)}\right)\right|\le\frac C{\log^2d}.$$
--
--   The root is strictly interior, so the real logarithm and divisions do not create endpoint roots. These formulas provide a scalar method to evaluate the optimal variance bound.
-- source:
--   Tight bound on relative entropy by entropy difference, arXiv:1304.0036v3, PDF p. 8, remark9

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P15

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Matrix ComplexConjugate ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Support50.P15

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

/-- Remark 9, PDF p.8, root characterization on p.25 and bounds on pp.23--24.
Asymptotic constants and thresholds precede dimension. -/
theorem remark9 :
    (∀ d : ℕ, 2 ≤ d → easyVariance d - 1 < maxVariance d ∧ maxVariance d < easyVariance d ∧
      (∃! r : ℝ, r ∈ Set.Ioo 0 (1 / 2) ∧
        (1 - 2 * r) * Real.log ((1 - r) / r * ((d : ℝ) - 1)) = 2) ∧
      (1 - 2 * optimalMass d) * Real.log ((1 - optimalMass d) / optimalMass d * ((d : ℝ) - 1)) = 2) ∧
    (∃ c > 0, ∃ d0 : ℕ, 3 ≤ d0 ∧ ∀ d ≥ d0,
      0 ≤ easyVariance d - maxVariance d ∧
      easyVariance d - maxVariance d ≤ c / (Real.log d) ^ 2 ∧
      |optimalMass d - (1 / 2 - 1 / Real.log ((d : ℝ) - 1))| ≤ c / (Real.log d) ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Support50.P15

end
