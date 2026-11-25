-- Prove2me | Theorems.Thm_SZ_digitY_even
-- name    : SZ.digitY_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:10:59.817246+00:00
-- url     : https://prove2.me/theorems/391fafa6-88a8-5c8c-8045-6231d5872445
-- title:
--   SZ: digit Y even
-- statement:
--   The SZ construction uses the digit Y even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SqrtThree.lean#L79-L80
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SqrtThree.lean#L79-L80

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_CoverGame
import Definitions.Def_SZ_SqrtThree
set_option autoImplicit false
open SZ

theorem SZ.digitY_even (i : ℕ) : Even (digitY i) := by sorry
