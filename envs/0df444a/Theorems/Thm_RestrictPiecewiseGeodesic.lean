-- Prove2me | Theorems.Thm_RestrictPiecewiseGeodesic
-- name    : RestrictPiecewiseGeodesic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:07:02.244559+00:00
-- url     : https://prove2.me/theorems/2ffdb34d-8438-452e-abba-fb2dfaf862c8
-- title:
--   Restrict Piecewise Geodesic: Restrict Piecewise Geodesic
-- statement:
--   Restricting a curve to the window between two breakpoints `s p, s q` of a given geodesic
--   resolution `(k,s)` yields a piecewise-geodesic curve resolved *by name* by the shifted resolution
--   `j ↦ s (p + j) - s p` into `q - p` edges: this is the prerequisite `RestrictLSI`'s piecewise-geodesic
--   conjunct needs (since `IsLSI` has piecewise-geodesicity as its first component), and the named form
--   is what lets `RestrictDeltaEpsNAtBreakpoints` count the edges of this very resolution.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/RestrictPiecewiseGeodesic.lean#L12-L63
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/RestrictPiecewiseGeodesic.lean#L12-L63

import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_IsGeodesicResolution
import Definitions.Def_Tablet_RestrictPiecewiseGeodesic
set_option autoImplicit false
open Set

theorem RestrictPiecewiseGeodesic {E : Type*} [MetricSpace E] (γ : Curve E)
    (k : ℕ) (s : ℕ → ℝ) (hres : IsGeodesicResolution γ k s) (p q : ℕ)
    (hpq : p ≤ q) (hqk : q ≤ k)
    (ha : 0 ≤ s p) (hab : s p ≤ s q) (hb : s q ≤ γ.len) :
    IsGeodesicResolution (curveRestrict γ (s p) (s q) ha hab hb) (q - p)
      (fun j => s (p + j) - s p) := by sorry
