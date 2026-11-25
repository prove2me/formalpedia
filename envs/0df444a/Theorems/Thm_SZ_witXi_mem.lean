-- Prove2me | Theorems.Thm_SZ_witXi_mem
-- name    : SZ.witXi_mem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:14:43.494654+00:00
-- url     : https://prove2.me/theorems/18a85806-49d4-44c7-8b56-c85e49c36d8e
-- title:
--   SZ: wit Xi mem
-- statement:
--   The witness is pinned to `[4/3, 5/3]`; the exact value, from the digit stream, is
--   `1.3416089979611266516309894306526154258451…` (`SZ/checks/dubD1O5-x3-leanrule.py`).
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SqrtThree.lean#L117-L119
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SqrtThree.lean#L117-L119

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_CoverGame
import Definitions.Def_SZ_SqrtThree
set_option autoImplicit false
open SZ

theorem SZ.witXi_mem : 4 / 3 ≤ witXi ∧ witXi ≤ 5 / 3 := by sorry
