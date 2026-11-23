-- Prove2me | Theorems.Thm_Relabel_orelabel_reduced
-- name    : Relabel.orelabel_reduced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:01:59.47313+00:00
-- url     : https://prove2.me/theorems/ed042a48-6f5c-43e1-9ebb-98ae67333c94
-- title:
--   Relabel: orelabel reduced
-- statement:
--   The Relabel construction uses the orelabel reduced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Relabel.lean#L413-L420
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Relabel.lean#L413-L420

import Definitions.Def_Bdd_Basic
import Definitions.Def_Bdd_Relabel
set_option autoImplicit true
attribute [local implicit_reducible] OBdd Bdd.Ordered Bdd.RelevantMayPrecede
open Relabel
attribute [local implicit_reducible] relabel relabel_heap relabel_node
attribute [local implicit_reducible] orelabel

theorem Relabel.orelabel_reduced {O : OBdd n m} {f : Nat → Nat} {hf : ∀ i : Fin n, f i < f n}
    {hu : ∀ i i' : Fin n, i < i' → O.1.usesVar i → O.1.usesVar i' → f i < f i'} :
    O.Reduced → (orelabel O hf hu).Reduced := by sorry
