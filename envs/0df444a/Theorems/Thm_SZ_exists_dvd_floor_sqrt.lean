-- Prove2me | Theorems.Thm_SZ_exists_dvd_floor_sqrt
-- name    : SZ.exists_dvd_floor_sqrt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T00:52:24.661797+00:00
-- url     : https://prove2.me/theorems/071444ce-4a11-47ba-a592-81d300be0e8d
-- title:
--   SZ: exists dvd floor sqrt
-- statement:
--   **Theorem C** ([Dub06EO]-style designed multiplier at a general modulus).  For `p ≥ 2`
--   and a non-square `m ≥ 3` satisfying (i) `p ∣ m - 1` and `p² ≤ m`, or (ii) `p ∣ m` and
--   `p(m-1) < (m-p)(1+√m)`, there is a real `ξ > 0` with `p ∣ ⌊ξ √mⁿ⌋` for every `n ≥ 1`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/ThmC.lean#L171-L189
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/ThmC.lean#L171-L189

import Definitions.Def_SZ_SliceHygiene
import Mathlib.Tactic.Push
import Mathlib.Tactic.IntervalCases
import Definitions.Def_SZ_ThmC
set_option autoImplicit false
open SZ

theorem SZ.exists_dvd_floor_sqrt (p : ℤ) (m : ℕ) (hp : 2 ≤ p) (hm : 3 ≤ m) (hns : ¬ IsSquare m)
    (hcase : (p ∣ (m : ℤ) - 1 ∧ p ^ 2 ≤ (m : ℤ)) ∨
      (p ∣ (m : ℤ) ∧ (p : ℝ) * ((m : ℝ) - 1) < ((m : ℝ) - (p : ℝ)) * (1 + Real.sqrt m))) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ n : ℕ, 1 ≤ n → p ∣ ⌊ξ * Real.sqrt m ^ n⌋ := by sorry
