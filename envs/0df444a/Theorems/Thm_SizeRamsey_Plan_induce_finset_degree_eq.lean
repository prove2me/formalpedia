-- Prove2me | Theorems.Thm_SizeRamsey_Plan_induce_finset_degree_eq
-- name    : SizeRamsey.Plan.induce_finset_degree_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:19:14.720872+00:00
-- url     : https://prove2.me/theorems/90f89ae3-af63-43de-8e77-19cdd28cc7d5
-- title:
--   Plan: induce finset degree eq
-- statement:
--   The Plan construction uses the induce finset degree eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L177-L180
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L177-L180

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

theorem SizeRamsey.Plan.induce_finset_degree_eq (D : Finset V) (v : (D : Set V)) :
    (G.induce (D : Set V)).degree v = ((G.neighborFinset v.val).filter (· ∈ D)).card := by sorry
