-- Prove2me | Theorems.Thm_RestrictDeltaEpsNAtBreakpoints
-- name    : RestrictDeltaEpsNAtBreakpoints
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:15:43.918725+00:00
-- url     : https://prove2.me/theorems/9dab7570-e3c5-44d4-9e9b-e11425dc49a7
-- title:
--   Restrict Delta Eps NAt Breakpoints: Restrict Delta Eps NAt Breakpoints
-- statement:
--   Restricting `γ` to the window between two breakpoints `s p, s q` of a geodesic resolution
--   `(k,s)` that linearly counts small edges is again a `(δ,ε,n)`-curve, provided the restricted arc
--   is non-closed (which discharges the closed-curve wrap clause of `IsDeltaEpsN` vacuously). The
--   general (non-breakpoint) restriction fails this inheritance: a restriction that truncates an edge
--   of `s` mid-edge can create a short edge for every `δ > 0` regardless of `n`.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/RestrictDeltaEpsNAtBreakpoints.lean#L12-L49
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/RestrictDeltaEpsNAtBreakpoints.lean#L12-L49

import Definitions.Def_Tablet_RestrictPiecewiseGeodesic
import Definitions.Def_Tablet_IsDeltaEpsN
import Definitions.Def_Tablet_RestrictDeltaEpsNAtBreakpoints
import Theorems.Thm_RestrictPiecewiseGeodesic

set_option autoImplicit false
open Set

theorem RestrictDeltaEpsNAtBreakpoints {E : Type*} [MetricSpace E] (γ : Curve E)
    (δ ε : ℝ) (n k : ℕ) (s : ℕ → ℝ)
    (hres : IsGeodesicResolution γ k s)
    (hcount : ∀ t t' : ℝ, 0 ≤ t → t ≤ t' → t' ≤ γ.len → t' - t ≤ 2 * ε⁻¹ * δ →
      ((Finset.Icc 1 k).filter
        (fun j => t ≤ s (j - 1) ∧ s j ≤ t' ∧ s j - s (j - 1) < δ)).card ≤ n)
    (p q : ℕ) (hpq : p ≤ q) (hqk : q ≤ k)
    (ha : 0 ≤ s p) (hab : s p ≤ s q) (hb : s q ≤ γ.len)
    (hnc : ¬ IsClosedCurve (curveRestrict γ (s p) (s q) ha hab hb)) :
    IsDeltaEpsN (curveRestrict γ (s p) (s q) ha hab hb) δ ε n := by sorry
