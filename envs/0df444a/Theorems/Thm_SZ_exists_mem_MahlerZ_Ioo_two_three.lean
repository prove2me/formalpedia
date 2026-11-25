-- Prove2me | Theorems.Thm_SZ_exists_mem_MahlerZ_Ioo_two_three
-- name    : SZ.exists_mem_MahlerZ_Ioo_two_three
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:36:33.157605+00:00
-- url     : https://prove2.me/theorems/4fd58d46-a13e-4042-be8d-da8c02ca879b
-- title:
--   SZ: exists mem Mahler Z Ioo two three
-- statement:
--   `𝒵` meets `(2,3)`: the paper's Corollary 6.1.  Since `[3,∞) ⊆ 𝒵`, any element of `𝒮`
--   above `2` would have to lie in this interval.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Cells.lean#L206-L207
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Cells.lean#L206-L207

import Definitions.Def_SZ_SliceHygiene
import Definitions.Def_SZ_SqrtTwo
import Definitions.Def_SZ_SqrtThree
import Definitions.Def_SZ_Tijdeman
import Mathlib.Tactic.IntervalCases
import Definitions.Def_SZ_Cells
set_option autoImplicit false
open SZ

theorem SZ.exists_mem_MahlerZ_Ioo_two_three : ∃ α ∈ MahlerZ, 2 < α ∧ α < 3 := by sorry
