-- Prove2me | Theorems.Thm_SizeRamsey_Plan_IsC4Map_rotate
-- name    : SizeRamsey.Plan.IsC4Map.rotate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:18:20.785262+00:00
-- url     : https://prove2.me/theorems/2d373ddc-98a8-571c-9989-be046b90c289
-- title:
--   Is C4 Map: rotate
-- statement:
--   The Is C4 Map construction uses the rotate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L40-L45
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L40-L45

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

theorem SizeRamsey.Plan.IsC4Map.rotate {G : SimpleGraph V} {f : Fin 4 → V} (hf : IsC4Map G f) (k : Fin 4) :
    IsC4Map G (fun i => f (i + k)) := by sorry
