-- Prove2me | Theorems.Thm_SizeRamsey_Plan_erase_degree_eq
-- name    : SizeRamsey.Plan.erase_degree_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:18:40.643015+00:00
-- url     : https://prove2.me/theorems/1f67a7b5-9620-4b20-9078-9d3f8f869517
-- title:
--   Plan: erase degree eq
-- statement:
--   The Plan construction uses the erase degree eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L170-L175
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L170-L175

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
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

theorem SizeRamsey.Plan.erase_degree_eq (D : Finset V) (v : {x : V // x ∉ D}) :
    (erase G D).degree v = ((G.neighborFinset v.val).filter (· ∉ D)).card := by sorry
