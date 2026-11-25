-- Prove2me | Theorems.Thm_SZ_floor_witXi_sqrtThree
-- name    : SZ.floor_witXi_sqrtThree
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:31:58.952025+00:00
-- url     : https://prove2.me/theorems/73f19f18-7852-5dca-b28b-1b5e964b50e1
-- title:
--   SZ: floor wit Xi sqrt Three
-- statement:
--   `⌊ξ √3⌋ = 2`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SqrtThree.lean#L184-L196
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SqrtThree.lean#L184-L196

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_CoverGame
import Definitions.Def_SZ_SqrtThree
set_option autoImplicit false
open SZ

theorem SZ.floor_witXi_sqrtThree : ⌊witXi * Real.sqrt 3⌋ = 2 := by sorry
