-- Prove2me | Theorems.Thm_SizeRamsey_Plan_sum_degrees_induce
-- name    : SizeRamsey.Plan.sum_degrees_induce
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:19:38.953802+00:00
-- url     : https://prove2.me/theorems/73921340-406f-5389-b5ea-1d5faf890bf2
-- title:
--   Plan: sum degrees induce
-- statement:
--   The Plan construction uses the sum degrees induce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L145-L150
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L145-L150

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

theorem SizeRamsey.Plan.sum_degrees_induce (s : Set V) :
    ∑ v ∈ Finset.univ.filter (· ∈ s), ((G.neighborFinset v).filter (· ∈ s)).card =
      2 * edgeCount (G.induce s) := by sorry
