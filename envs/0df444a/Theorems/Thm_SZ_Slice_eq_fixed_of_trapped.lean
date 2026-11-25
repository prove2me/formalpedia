-- Prove2me | Theorems.Thm_SZ_Slice_eq_fixed_of_trapped
-- name    : SZ.Slice.eq_fixed_of_trapped
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:56:45.740039+00:00
-- url     : https://prove2.me/theorems/e82ba805-4e68-4b55-b423-09ab04caeac0
-- title:
--   Slice: eq fixed of trapped
-- statement:
--   If from step `K` on the orbit obeys one affine `r`-expanding map, `r > 1`, and stays
--   bounded, it sits at that map's fixed point `c/(r-1)`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SliceHygiene.lean#L59-L79
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SliceHygiene.lean#L59-L79

import Definitions.Def_SZ_Slice
import Mathlib.Tactic.Push
import Definitions.Def_SZ_SliceHygiene
set_option autoImplicit false
open SZ
open SZ.Slice

theorem SZ.Slice.eq_fixed_of_trapped {f : ℕ → ℝ} {r c D : ℝ} {K : ℕ} (hr : 1 < r)
    (hrec : ∀ k, K ≤ k → f (k + 1) = r * f k - c)
    (hbd : ∀ k, K ≤ k → |f k - c / (r - 1)| ≤ D) : f K = c / (r - 1) := by sorry
