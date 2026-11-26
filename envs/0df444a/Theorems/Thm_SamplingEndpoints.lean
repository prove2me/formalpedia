-- Prove2me | Theorems.Thm_SamplingEndpoints
-- name    : SamplingEndpoints
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:55:59.42713+00:00
-- url     : https://prove2.me/theorems/96bdbb27-43c9-534d-82d2-1d69fc1669bb
-- title:
--   Sampling Endpoints: Sampling Endpoints
-- statement:
--   The piecewise-geodesic sampling `γ^δ` has the same start and end points as `γ` (paper.tex
--   lines 1327 and 1441, both asserted without proof).
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/SamplingEndpoints.lean#L8-L44
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/SamplingEndpoints.lean#L8-L44

import Definitions.Def_Tablet_curveSampling
import Definitions.Def_Tablet_SamplingEndpoints
set_option autoImplicit false
open Set

theorem SamplingEndpoints {E : Type*} [MetricSpace E] (GP : GeodesicPairing E)
    (γ : Curve E) (δ : ℝ) (hδ0 : 0 < δ) (hδlen : δ < γ.len) :
    (curveSampling GP γ δ hδ0 hδlen).toFun 0 = γ.toFun 0 ∧
      (curveSampling GP γ δ hδ0 hδlen).toFun (curveSampling GP γ δ hδ0 hδlen).len
        = γ.toFun γ.len := by sorry
