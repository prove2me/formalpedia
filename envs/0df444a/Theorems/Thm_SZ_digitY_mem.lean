-- Prove2me | Theorems.Thm_SZ_digitY_mem
-- name    : SZ.digitY_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:29:15.046726+00:00
-- url     : https://prove2.me/theorems/c52904cc-d357-4e56-bc61-27565ed1699b
-- title:
--   SZ: digit Y mem
-- statement:
--   The SZ construction uses the digit Y mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SqrtThree.lean#L76-L77
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SqrtThree.lean#L76-L77

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_CoverGame
import Definitions.Def_SZ_SqrtThree
set_option autoImplicit false
open SZ

theorem SZ.digitY_mem (i : ℕ) : digitY i = 0 ∨ digitY i = 2 := by sorry
