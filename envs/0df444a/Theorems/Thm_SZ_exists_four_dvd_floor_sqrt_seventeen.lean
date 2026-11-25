-- Prove2me | Theorems.Thm_SZ_exists_four_dvd_floor_sqrt_seventeen
-- name    : SZ.exists_four_dvd_floor_sqrt_seventeen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:03:14.781291+00:00
-- url     : https://prove2.me/theorems/bbce0186-ebd4-596e-806e-38d83e099594
-- title:
--   SZ: exists four dvd floor sqrt seventeen
-- statement:
--   `p = 4`, `m = 17 = 4² + 1`: branch (i).
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/ThmC.lean#L292-L298
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/ThmC.lean#L292-L298

import Definitions.Def_SZ_SliceHygiene
import Mathlib.Tactic.Push
import Mathlib.Tactic.IntervalCases
import Definitions.Def_SZ_ThmC
set_option autoImplicit false
open SZ

theorem SZ.exists_four_dvd_floor_sqrt_seventeen :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ n : ℕ, 1 ≤ n → (4 : ℤ) ∣ ⌊ξ * Real.sqrt 17 ^ n⌋ := by sorry
