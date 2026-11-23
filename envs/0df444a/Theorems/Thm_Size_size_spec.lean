-- Prove2me | Theorems.Thm_Size_size_spec
-- name    : Size.size_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:08:22.280459+00:00
-- url     : https://prove2.me/theorems/ee7e1e40-d1fd-42d8-b4da-e36fad43ef7b
-- title:
--   Size: size spec
-- statement:
--   The Size construction uses the size spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Size.lean#L25-L39
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Size.lean#L25-L39

import Definitions.Def_Bdd_Collect
import Definitions.Def_Bdd_Size
set_option autoImplicit true
open Size

theorem Size.size_spec {O : OBdd n m} : size O = OBdd.size O := by sorry
