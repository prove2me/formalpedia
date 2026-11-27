-- Prove2me | Theorems.Thm_SizeRamsey_Plan_tau4_delete_leaf_vertex
-- name    : SizeRamsey.Plan.tau4_delete_leaf_vertex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:25:53.650771+00:00
-- url     : https://prove2.me/theorems/951efa48-c649-486b-8a65-86bc8ffcb83a
-- title:
--   Plan: tau4 delete leaf vertex
-- statement:
--   The Plan construction uses the tau4 delete leaf vertex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L328-L348
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L328-L348

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

theorem SizeRamsey.Plan.tau4_delete_leaf_vertex
    (v : V) (hd : G.degree v ≤ 1) :
    tau4 (erase G {v}) = tau4 G := by sorry
