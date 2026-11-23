-- Prove2me | Theorems.Thm_Size_size_node_le
-- name    : Size.size_node_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:08:29.56546+00:00
-- url     : https://prove2.me/theorems/e7b92388-a3b6-49b7-86ee-d535e2c4095b
-- title:
--   Size: size node le
-- statement:
--   The Size construction uses the size node le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Size.lean#L41-L80
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Size.lean#L41-L80

import Definitions.Def_Bdd_Collect
import Definitions.Def_Bdd_Size
set_option autoImplicit true
open Size

theorem Size.size_node_le {O : OBdd n m} {h : O.1.root = .node j} :
    size O ≤ 1 + (size (O.low h)) + (size (O.high h)) := by sorry
