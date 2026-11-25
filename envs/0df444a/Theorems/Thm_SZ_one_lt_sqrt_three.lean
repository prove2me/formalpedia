-- Prove2me | Theorems.Thm_SZ_one_lt_sqrt_three
-- name    : SZ.one_lt_sqrt_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:12:14.619402+00:00
-- url     : https://prove2.me/theorems/280b3fac-b850-566c-9b51-479010681062
-- title:
--   SZ: one lt sqrt three
-- statement:
--   The SZ construction uses the one lt sqrt three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SqrtThree.lean#L159-L161
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SqrtThree.lean#L159-L161

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_CoverGame
import Definitions.Def_SZ_SqrtThree
set_option autoImplicit false
open SZ

theorem SZ.one_lt_sqrt_three : (1 : ℝ) < Real.sqrt 3 := by sorry
