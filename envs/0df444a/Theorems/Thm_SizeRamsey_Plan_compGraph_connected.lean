-- Prove2me | Theorems.Thm_SizeRamsey_Plan_compGraph_connected
-- name    : SizeRamsey.Plan.compGraph_connected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:21:11.592636+00:00
-- url     : https://prove2.me/theorems/7d162002-6ff1-53a6-8cf0-9dd3a2524f96
-- title:
--   Plan: comp Graph connected
-- statement:
--   The Plan construction uses the comp Graph connected property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Components.lean#L86-L88
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Components.lean#L86-L88

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
omit [Fintype V]

theorem SizeRamsey.Plan.compGraph_connected (C : G.ConnectedComponent) :
    (compGraph G C).Connected := by sorry
