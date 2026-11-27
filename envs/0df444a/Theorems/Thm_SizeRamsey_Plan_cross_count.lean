-- Prove2me | Theorems.Thm_SizeRamsey_Plan_cross_count
-- name    : SizeRamsey.Plan.cross_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:19:18.317254+00:00
-- url     : https://prove2.me/theorems/e2dd68d2-52c2-45bb-adcb-4f1f6a5454f0
-- title:
--   Plan: cross count
-- statement:
--   The Plan construction uses the cross count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L160-L168
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L160-L168

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

theorem SizeRamsey.Plan.cross_count (D : Finset V) :
    ∑ v ∈ Finset.univ.filter (· ∉ D), ((G.neighborFinset v).filter (· ∈ D)).card =
      ∑ v ∈ D, ((G.neighborFinset v).filter (· ∉ D)).card := by sorry
