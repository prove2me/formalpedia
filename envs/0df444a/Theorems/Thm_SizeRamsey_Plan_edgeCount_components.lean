-- Prove2me | Theorems.Thm_SizeRamsey_Plan_edgeCount_components
-- name    : SizeRamsey.Plan.edgeCount_components
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:21:08.839987+00:00
-- url     : https://prove2.me/theorems/301809bd-4094-5cb5-8e66-37b51675e04d
-- title:
--   Plan: edge Count components
-- statement:
--   The Plan construction uses the edge Count components property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Components.lean#L65-L83
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Components.lean#L65-L83

module
public import Definitions.Def_SizeRamsey_Deletion
public import Definitions.Def_SizeRamsey_Components
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

theorem SizeRamsey.Plan.edgeCount_components :
    edgeCount G =
      ∑ C : G.ConnectedComponent, edgeCount (compGraph G C) := by sorry
