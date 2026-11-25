-- Prove2me | Theorems.Thm_SZ_sqrt_natCast_mem_MahlerZ
-- name    : SZ.sqrt_natCast_mem_MahlerZ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:14:42.312685+00:00
-- url     : https://prove2.me/theorems/b5129791-0fef-5b99-a68d-f75f88ead80a
-- title:
--   SZ: sqrt nat Cast mem Mahler Z
-- statement:
--   Every `√m` with `m ≥ 2` an integer other than `2` lies in `𝒵`: the perfect squares
--   trivially, `m = 3` by `SZ.sqrtThree_mem_MahlerZ`, the four cells `{5,6,7,8}` by the cover
--   game above, and `m ≥ 9` because then `√m ≥ 3`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Cells.lean#L214-L231
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Cells.lean#L214-L231

import Definitions.Def_SZ_SliceHygiene
import Definitions.Def_SZ_SqrtTwo
import Definitions.Def_SZ_SqrtThree
import Definitions.Def_SZ_Tijdeman
import Mathlib.Tactic.IntervalCases
import Definitions.Def_SZ_Cells
set_option autoImplicit false
open SZ

theorem SZ.sqrt_natCast_mem_MahlerZ {m : ℕ} (hm : 2 ≤ m) (hne : m ≠ 2) :
    Real.sqrt m ∈ MahlerZ := by sorry
