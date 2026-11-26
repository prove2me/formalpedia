-- Prove2me | Theorems.Thm_RestrictGeodesicResolutionTruncated
-- name    : RestrictGeodesicResolutionTruncated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:02:04.583182+00:00
-- url     : https://prove2.me/theorems/19ee7817-f183-58c8-8ecf-b985f788bed6
-- title:
--   Restrict Geodesic Resolution Truncated: Restrict Geodesic Resolution Truncated
-- statement:
--   **Truncated-end sub-resolution.** If `(k,s)` is a geodesic resolution of `η` and
--   `0 ≤ a < b ≤ η.len`, then for *any* indices `jA, jB` with `jA < k`, `s jA ≤ a ≤ s (jA+1)`,
--   `1 ≤ jB ≤ k` and `s (jB-1) ≤ b ≤ s jB`, the restriction `η|_{[a,b]}` is resolved into `jB - jA`
--   geodesic edges by the explicitly named breakpoint function which is `0` at index `0`, `b - a` at
--   the top index `jB - jA`, and the shifted genuine breakpoint `s (jA + i) - a` at every intermediate
--   index. Only the first and last edges are truncated; all others are literal shifts of full edges
--   of `s`.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/RestrictGeodesicResolutionTruncated.lean#L14-L134
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/RestrictGeodesicResolutionTruncated.lean#L14-L134

import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_IsGeodesicResolution
import Definitions.Def_Tablet_RestrictGeodesicResolutionTruncated
set_option autoImplicit false
open Set

theorem RestrictGeodesicResolutionTruncated {E : Type*} [MetricSpace E] (η : Curve E)
    (k : ℕ) (s : ℕ → ℝ) (hres : IsGeodesicResolution η k s)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ η.len)
    (jA jB : ℕ) (hjAk : jA < k) (hsjA : s jA ≤ a) (hajA : a ≤ s (jA + 1))
    (hjB1 : 1 ≤ jB) (hjBk : jB ≤ k) (hsjB : s (jB - 1) ≤ b) (hbjB : b ≤ s jB) :
    IsGeodesicResolution (curveRestrict η a b ha hab.le hb) (jB - jA)
      (fun i => if i = 0 then 0 else if i = jB - jA then b - a else s (jA + i) - a) := by sorry
