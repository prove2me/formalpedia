-- Prove2me | Theorems.Thm_SZ_floor_witXi_three
-- name    : SZ.floor_witXi_three
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:33:54.499417+00:00
-- url     : https://prove2.me/theorems/de374021-1337-5e62-bb18-269aa2f4b25f
-- title:
--   SZ: floor wit Xi three
-- statement:
--   `⌊3 ξ⌋ = ⌊ξ (√3)²⌋ = 4`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SqrtThree.lean#L199-L207
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SqrtThree.lean#L199-L207

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_CoverGame
import Definitions.Def_SZ_SqrtThree
set_option autoImplicit false
open SZ

theorem SZ.floor_witXi_three : ⌊witXi * Real.sqrt 3 ^ 2⌋ = 4 := by sorry
