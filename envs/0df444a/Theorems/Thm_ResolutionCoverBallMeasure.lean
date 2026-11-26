-- Prove2me | Theorems.Thm_ResolutionCoverBallMeasure
-- name    : ResolutionCoverBallMeasure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:10:47.914546+00:00
-- url     : https://prove2.me/theorems/4e65d3e7-b862-5eab-a21b-e5a6ac6d9c20
-- title:
--   Resolution Cover Ball Measure: Resolution Cover Ball Measure
-- statement:
--   From a covering of the part of `γ` lying in a closed ball by finitely many edges of a geodesic
--   resolution, a Morrey-type bound on the ball's `μ_γ`-measure: each edge contributes at most `2r`
--   (by `GeodesicMorreyLeTwo`), and subadditivity of Lebesgue measure over the index set assembles
--   these into `μ_γ(B) ≤ 2 |J| r`.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/ResolutionCoverBallMeasure.lean#L14-L80
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/ResolutionCoverBallMeasure.lean#L14-L80

import Definitions.Def_Tablet_IsGeodesicResolution
import Definitions.Def_Tablet_GeodesicMorreyLeTwo
import Definitions.Def_Tablet_curveMeasure
import Definitions.Def_Tablet_CurveLipschitz
import Definitions.Def_Tablet_morreyNorm
import Definitions.Def_Tablet_ResolutionCoverBallMeasure
import Theorems.Thm_CurveLipschitz
import Theorems.Thm_GeodesicMorreyLeTwo

set_option autoImplicit false
open MeasureTheory Set ENNReal

theorem ResolutionCoverBallMeasure {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (γ : Curve E) (k : ℕ) (s : ℕ → ℝ) (hres : IsGeodesicResolution γ k s)
    (J : Finset ℕ) (hJ : J ⊆ Finset.Icc 1 k) (x : E) (r : ℝ) (hr : 0 < r)
    (hcov : {u ∈ Set.Icc (0:ℝ) γ.len | γ.toFun u ∈ Metric.closedBall x r} ⊆
      ⋃ j ∈ J, Set.Icc (s (j - 1)) (s j)) :
    curveMeasure γ (Metric.closedBall x r) ≤ ENNReal.ofReal (2 * (J.card : ℝ) * r) := by sorry
