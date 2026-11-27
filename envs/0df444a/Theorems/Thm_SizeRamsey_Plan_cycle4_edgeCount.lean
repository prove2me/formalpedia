-- Prove2me | Theorems.Thm_SizeRamsey_Plan_cycle4_edgeCount
-- name    : SizeRamsey.Plan.cycle4_edgeCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:22:58.344002+00:00
-- url     : https://prove2.me/theorems/d98ce329-44f9-5f82-8f6f-1a781d04722e
-- title:
--   Plan: cycle4 edge Count
-- statement:
--   The Plan construction uses the cycle4 edge Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/SmallGraphs.lean#L26-L27
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/SmallGraphs.lean#L26-L27

module
public import Definitions.Def_SizeRamsey_FiniteChecks
public import Definitions.Def_SizeRamsey_SmallGraphs
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v

theorem SizeRamsey.Plan.cycle4_edgeCount : edgeCount (SimpleGraph.cycleGraph 4) = 4 := by sorry
