-- Prove2me | Theorems.Thm_SZ_exists_eventually_composite_sqrt
-- name    : SZ.exists_eventually_composite_sqrt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:02:57.42675+00:00
-- url     : https://prove2.me/theorems/6e49142c-5449-5122-88c9-af1c2788dfb8
-- title:
--   SZ: exists eventually composite sqrt
-- statement:
--   **Theorem C, the corollary.**  The designed integral parts `⌊ξ √mⁿ⌋` are composite for
--   every sufficiently large `n`: they are divisible by `p` and eventually exceed `p`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/ThmC.lean#L193-L225
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/ThmC.lean#L193-L225

import Definitions.Def_SZ_SliceHygiene
import Mathlib.Tactic.Push
import Mathlib.Tactic.IntervalCases
import Definitions.Def_SZ_ThmC
set_option autoImplicit false
open SZ

theorem SZ.exists_eventually_composite_sqrt (p : ℤ) (m : ℕ) (hp : 2 ≤ p) (hm : 3 ≤ m)
    (hns : ¬ IsSquare m)
    (hcase : (p ∣ (m : ℤ) - 1 ∧ p ^ 2 ≤ (m : ℤ)) ∨
      (p ∣ (m : ℤ) ∧ (p : ℝ) * ((m : ℝ) - 1) < ((m : ℝ) - (p : ℝ)) * (1 + Real.sqrt m))) :
    ∃ ξ : ℝ, 0 < ξ ∧ (∀ n : ℕ, 1 ≤ n → p ∣ ⌊ξ * Real.sqrt m ^ n⌋) ∧
      ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
        ∃ a b : ℤ, 1 < a ∧ 1 < b ∧ ⌊ξ * Real.sqrt m ^ n⌋ = a * b := by sorry
