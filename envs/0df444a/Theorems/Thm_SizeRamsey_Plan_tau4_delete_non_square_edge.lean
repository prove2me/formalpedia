-- Prove2me | Theorems.Thm_SizeRamsey_Plan_tau4_delete_non_square_edge
-- name    : SizeRamsey.Plan.tau4_delete_non_square_edge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:20:33.430767+00:00
-- url     : https://prove2.me/theorems/28af4c06-9f8c-42f1-9b38-89d64c4927bf
-- title:
--   Plan: tau4 delete non square edge
-- statement:
--   The Plan construction uses the tau4 delete non square edge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L300-L326
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L300-L326

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

theorem SizeRamsey.Plan.tau4_delete_non_square_edge
    {u v : V} (hadj : G.Adj u v)
    (h : ¬ EdgeOnSquare G u v) :
    tau4 (G.deleteEdges {s(u, v)}) = tau4 G ∧
    edgeCount (G.deleteEdges {s(u, v)}) + 1 = edgeCount G := by sorry
