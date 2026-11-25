-- Prove2me | Theorems.Thm_SZ_isDigits_digitY
-- name    : SZ.isDigits_digitY
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:29:18.694385+00:00
-- url     : https://prove2.me/theorems/60edd6d2-7339-4165-a126-99ca41119a38
-- title:
--   SZ: is Digits digit Y
-- statement:
--   The SZ construction uses the is Digits digit Y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SqrtThree.lean#L82-L85
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SqrtThree.lean#L82-L85

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_CoverGame
import Definitions.Def_SZ_SqrtThree
set_option autoImplicit false
open SZ

theorem SZ.isDigits_digitY : IsDigits 3 digitY := by sorry
