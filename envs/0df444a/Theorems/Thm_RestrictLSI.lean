-- Prove2me | Theorems.Thm_RestrictLSI
-- name    : RestrictLSI
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:10:39.871083+00:00
-- url     : https://prove2.me/theorems/44a9cb7a-2ffd-53ac-8a72-3dcedf0cf394
-- title:
--   Restrict LSI: Restrict LSI
-- statement:
--   If `γ` restricted to `[t,t']` is `(δ,ε)`-large-scale-invertible and non-closed, and `[u,u']`
--   is a non-closed sub-window of `[t,t']` on which `γ` restricts to a piecewise-geodesic curve, then
--   `γ` restricted to `[u,u']` is again `(δ,ε)`-large-scale-invertible. Both conclusions are stated as
--   direct restrictions of the same ambient curve `γ` (not as a nested restriction of the restriction)
--   so that this and `RestrictDeltaEpsNAtBreakpoints` feed `FullBallLem` on one and the same term.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/RestrictLSI.lean#L13-L61
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/RestrictLSI.lean#L13-L61

import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_IsLSI
import Definitions.Def_Tablet_IsPiecewiseGeodesic
import Definitions.Def_Tablet_RestrictLSI
set_option autoImplicit false
open Set

theorem RestrictLSI {E : Type*} [MetricSpace E] (γ : Curve E) (δ ε : ℝ)
    (t t' u u' : ℝ)
    (ht : 0 ≤ t) (htt' : t ≤ t') (ht'l : t' ≤ γ.len)
    (hu : t ≤ u) (huu' : u ≤ u') (hu't : u' ≤ t')
    (hu0 : 0 ≤ u) (hu'l : u' ≤ γ.len)
    (hlsi : IsLSI (curveRestrict γ t t' ht htt' ht'l) δ ε)
    (hnct : ¬ IsClosedCurve (curveRestrict γ t t' ht htt' ht'l))
    (hncu : ¬ IsClosedCurve (curveRestrict γ u u' hu0 huu' hu'l))
    (hpg : IsPiecewiseGeodesic (curveRestrict γ u u' hu0 huu' hu'l)) :
    IsLSI (curveRestrict γ u u' hu0 huu' hu'l) δ ε := by sorry
