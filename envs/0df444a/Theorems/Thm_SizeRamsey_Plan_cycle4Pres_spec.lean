-- Prove2me | Theorems.Thm_SizeRamsey_Plan_cycle4Pres_spec
-- name    : SizeRamsey.Plan.cycle4Pres_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:23:16.89491+00:00
-- url     : https://prove2.me/theorems/2c414aae-a827-4ad2-82f0-c16ac095d156
-- title:
--   Plan: cycle4 Pres spec
-- statement:
--   The Plan construction uses the cycle4 Pres spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/SmallGraphs.lean#L48-L50
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/SmallGraphs.lean#L48-L50

module
public import Definitions.Def_SizeRamsey_FiniteChecks
public import Definitions.Def_SizeRamsey_SmallGraphs
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v

theorem SizeRamsey.Plan.cycle4Pres_spec : ∀ v, v ∈ cycle4Pres v ∧ (cycle4Pres v).card = 1 ∧
    QTrans (SimpleGraph.cycleGraph 4) (cycle4Pres v) := by sorry
