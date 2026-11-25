-- Prove2me | Theorems.Thm_SZ_exists_five_dvd_floor_sqrt_twentySix
-- name    : SZ.exists_five_dvd_floor_sqrt_twentySix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:03:29.887071+00:00
-- url     : https://prove2.me/theorems/c98dd712-0faf-4d8c-b0ca-3693f4d2c12a
-- title:
--   SZ: exists five dvd floor sqrt twenty Six
-- statement:
--   `p = 5`, `m = 26 = 5² + 1`: branch (i).
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/ThmC.lean#L301-L307
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/ThmC.lean#L301-L307

import Definitions.Def_SZ_SliceHygiene
import Mathlib.Tactic.Push
import Mathlib.Tactic.IntervalCases
import Definitions.Def_SZ_ThmC
set_option autoImplicit false
open SZ

theorem SZ.exists_five_dvd_floor_sqrt_twentySix :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ n : ℕ, 1 ≤ n → (5 : ℤ) ∣ ⌊ξ * Real.sqrt 26 ^ n⌋ := by sorry
