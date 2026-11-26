-- Prove2me | Theorems.Thm_SamplingPiecewiseGeodesic
-- name    : SamplingPiecewiseGeodesic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:58:46.500866+00:00
-- url     : https://prove2.me/theorems/c5163e1a-c77d-5195-9c09-aa8f014f6d24
-- title:
--   Sampling Piecewise Geodesic: Sampling Piecewise Geodesic
-- statement:
--   The piecewise-geodesic sampling `γ^δ` of `γ` is itself piecewise geodesic (paper.tex line 1233
--   Definition 4.3: `γ^δ` is built as a chain of geodesic edges, hence manifestly piecewise geodesic;
--   needed so `BBAssertion`/`ClosingUp` can supply the `IsPiecewiseGeodesic` half of the paper's
--   "piecewise-geodesic closed curves" conclusion).
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/SamplingPiecewiseGeodesic.lean#L13-L27
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/SamplingPiecewiseGeodesic.lean#L13-L27

import Definitions.Def_Tablet_curveSampling
import Definitions.Def_Tablet_IsPiecewiseGeodesic
import Definitions.Def_Tablet_GeodesicIsPiecewiseGeodesic
import Definitions.Def_Tablet_ConcatPiecewiseGeodesic
import Definitions.Def_Tablet_SamplingPiecewiseGeodesic
import Theorems.Thm_ConcatPiecewiseGeodesic
import Theorems.Thm_GeodesicIsPiecewiseGeodesic

set_option autoImplicit false
open Set

theorem SamplingPiecewiseGeodesic {E : Type*} [MetricSpace E] (GP : GeodesicPairing E)
    (γ : Curve E) (δ : ℝ) (hδ0 : 0 < δ) (hδlen : δ < γ.len) :
    IsPiecewiseGeodesic (curveSampling GP γ δ hδ0 hδlen) := by sorry
