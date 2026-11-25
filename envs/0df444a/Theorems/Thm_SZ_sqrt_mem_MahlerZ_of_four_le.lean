-- Prove2me | Theorems.Thm_SZ_sqrt_mem_MahlerZ_of_four_le
-- name    : SZ.sqrt_mem_MahlerZ_of_four_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:03:06.666509+00:00
-- url     : https://prove2.me/theorems/b66fa031-fc3a-4237-a731-567e1faabf11
-- title:
--   SZ: sqrt mem Mahler Z of four le
-- statement:
--   **The uniform greedy of the paper's proof of Theorem B**, as a corollary of Theorem C
--   at `p = 2`: branch (i) serves the odd bases (`2 ∣ m - 1` and `4 ≤ m`), branch (ii) the even
--   ones, where `(m-2)(1+√m) - 2(m-1) = √m(√m-2)(√m+1) > 0`.  `SZ/Cells.lean` reaches `m ≥ 9`
--   by the shorter route through `[3,∞) ⊆ 𝒵` (`SZ.mem_MahlerZ_of_three_le`); this is the same
--   statement proved the way the paper prints it.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/ThmC.lean#L234-L262
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/ThmC.lean#L234-L262

import Definitions.Def_SZ_SliceHygiene
import Mathlib.Tactic.Push
import Mathlib.Tactic.IntervalCases
import Definitions.Def_SZ_ThmC
set_option autoImplicit false
open SZ

theorem SZ.sqrt_mem_MahlerZ_of_four_le {m : ℕ} (hm : 4 ≤ m) (hns : ¬ IsSquare m) :
    Real.sqrt m ∈ MahlerZ := by sorry
