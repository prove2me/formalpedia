-- Prove2me | Theorems.Thm_SizeRamsey_Plan_erase_edgeCount
-- name    : SizeRamsey.Plan.erase_edgeCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:19:51.698574+00:00
-- url     : https://prove2.me/theorems/cad5fbdb-8358-4c66-9193-792964e8492a
-- title:
--   Plan: erase edge Count
-- statement:
--   The Plan construction uses the erase edge Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L225-L255
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L225-L255

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

theorem SizeRamsey.Plan.erase_edgeCount (D : Finset V) :
    edgeCount (erase G D) + (∑ v ∈ D, G.degree v) =
      edgeCount G + edgeCount (G.induce (D : Set V)) := by sorry
