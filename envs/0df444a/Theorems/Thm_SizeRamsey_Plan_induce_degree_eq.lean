-- Prove2me | Theorems.Thm_SizeRamsey_Plan_induce_degree_eq
-- name    : SizeRamsey.Plan.induce_degree_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:18:25.775812+00:00
-- url     : https://prove2.me/theorems/c87f9a4b-3349-4082-a31d-21a4fbefa7d1
-- title:
--   Plan: induce degree eq
-- statement:
--   The Plan construction uses the induce degree eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L131-L143
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L131-L143

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

theorem SizeRamsey.Plan.induce_degree_eq (s : Set V) (v : s) :
    (G.induce s).degree v = ((G.neighborFinset v.val).filter (· ∈ s)).card := by sorry
