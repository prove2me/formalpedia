-- Prove2me | Theorems.Thm_SizeRamsey_Plan_IsC4Map_erase_val
-- name    : SizeRamsey.Plan.IsC4Map.erase_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:18:24.468379+00:00
-- url     : https://prove2.me/theorems/b3227eee-4725-42e8-b95f-78efcabb9027
-- title:
--   Is C4 Map: erase val
-- statement:
--   The Is C4 Map construction uses the erase val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L70-L72
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L70-L72

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

theorem SizeRamsey.Plan.IsC4Map.erase_val {G : SimpleGraph V} {D : Finset V} {f : Fin 4 → {v : V // v ∉ D}}
    (hf : IsC4Map (erase G D) f) : IsC4Map G (fun i => (f i : V)) := by sorry
