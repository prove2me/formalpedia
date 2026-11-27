-- Prove2me | Theorems.Thm_SizeRamsey_Plan_IsC4Map_erase_mk
-- name    : SizeRamsey.Plan.IsC4Map.erase_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:18:22.887771+00:00
-- url     : https://prove2.me/theorems/974a0be3-26ff-4ae4-9a40-83600951c8ff
-- title:
--   Is C4 Map: erase mk
-- statement:
--   The Is C4 Map construction uses the erase mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L74-L77
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L74-L77

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

theorem SizeRamsey.Plan.IsC4Map.erase_mk {G : SimpleGraph V} {D : Finset V} {f : Fin 4 → V}
    (hf : IsC4Map G f) (h : ∀ i, f i ∉ D) :
    IsC4Map (erase G D) (fun i => (⟨f i, h i⟩ : {v : V // v ∉ D})) := by sorry
