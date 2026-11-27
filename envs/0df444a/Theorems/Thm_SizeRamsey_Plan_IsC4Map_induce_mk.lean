-- Prove2me | Theorems.Thm_SizeRamsey_Plan_IsC4Map_induce_mk
-- name    : SizeRamsey.Plan.IsC4Map.induce_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:18:44.974853+00:00
-- url     : https://prove2.me/theorems/f4ac7eab-86e0-54d2-be82-ea0397a87193
-- title:
--   Is C4 Map: induce mk
-- statement:
--   The Is C4 Map construction uses the induce mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L65-L68
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L65-L68

module
public import Definitions.Def_SizeRamsey_Basic
public import Definitions.Def_SizeRamsey_Deletion
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
variable {V : Type*} {W : Type*}

theorem SizeRamsey.Plan.IsC4Map.induce_mk {G : SimpleGraph V} {s : Set V} {f : Fin 4 → V}
    (hf : IsC4Map G f) (h : ∀ i, f i ∈ s) : IsC4Map (G.induce s) (fun i => ⟨f i, h i⟩) := by sorry
