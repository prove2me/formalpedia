-- Prove2me | Theorems.Thm_Size_size_le
-- name    : Size.size_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:09:20.954789+00:00
-- url     : https://prove2.me/theorems/e73e7587-0255-42e5-83ef-7a2762514563
-- title:
--   Size: size le
-- statement:
--   The Size construction uses the size le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Size.lean#L130-L134
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Size.lean#L130-L134

import Definitions.Def_Bdd_Collect
import Definitions.Def_Bdd_Size
set_option autoImplicit true
open Size

theorem Size.size_le {O : OBdd n m} : size O ≤ 2 ^ n - 1 := by sorry
