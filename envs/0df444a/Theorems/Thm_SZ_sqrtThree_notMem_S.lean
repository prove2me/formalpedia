-- Prove2me | Theorems.Thm_SZ_sqrtThree_notMem_S
-- name    : SZ.sqrtThree_notMem_S
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:31:45.018409+00:00
-- url     : https://prove2.me/theorems/5adfea16-98c5-4630-a7c5-66aa730cd609
-- title:
--   SZ: sqrt Three not Mem S
-- statement:
--   The complementary statement: `√3 ∉ 𝒮`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SqrtThree.lean#L179-L179
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SqrtThree.lean#L179-L179

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_CoverGame
import Definitions.Def_SZ_SqrtThree
set_option autoImplicit false
open SZ

theorem SZ.sqrtThree_notMem_S : Real.sqrt 3 ∉ S := by sorry
