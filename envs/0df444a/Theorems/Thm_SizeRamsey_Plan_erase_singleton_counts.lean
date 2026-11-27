-- Prove2me | Theorems.Thm_SizeRamsey_Plan_erase_singleton_counts
-- name    : SizeRamsey.Plan.erase_singleton_counts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:20:29.146146+00:00
-- url     : https://prove2.me/theorems/2e077907-89fe-4782-b5b4-3ad091b39ff8
-- title:
--   Plan: erase singleton counts
-- statement:
--   The Plan construction uses the erase singleton counts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L257-L291
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L257-L291

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

theorem SizeRamsey.Plan.erase_singleton_counts (v : V) :
    edgeCount (erase G {v}) + G.degree v = edgeCount G ∧
    edgeCount (erase G {v}) =
      edgeCount (G.deleteIncidenceSet v) ∧
    tau4 (erase G {v}) =
      tau4 (G.deleteIncidenceSet v) := by sorry
