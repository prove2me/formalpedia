-- Prove2me | Theorems.Thm_SizeRamsey_Plan_IsC4Map_edgeOnSquare
-- name    : SizeRamsey.Plan.IsC4Map.edgeOnSquare
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:18:43.751016+00:00
-- url     : https://prove2.me/theorems/efc5f7c3-9893-43f5-86bd-44645cdeca8c
-- title:
--   Is C4 Map: edge On Square
-- statement:
--   The Is C4 Map construction uses the edge On Square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L55-L58
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L55-L58

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

theorem SizeRamsey.Plan.IsC4Map.edgeOnSquare {G : SimpleGraph V} {f : Fin 4 → V} (hf : IsC4Map G f)
    (i : Fin 4) : EdgeOnSquare G (f i) (f (i + 1)) ∧ EdgeOnSquare G (f (i + 1)) (f i) := by sorry
