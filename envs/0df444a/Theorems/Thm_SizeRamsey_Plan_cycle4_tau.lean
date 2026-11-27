-- Prove2me | Theorems.Thm_SizeRamsey_Plan_cycle4_tau
-- name    : SizeRamsey.Plan.cycle4_tau
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:23:26.999778+00:00
-- url     : https://prove2.me/theorems/41a93dde-090c-557e-ad63-776dbb2fc8a4
-- title:
--   Plan: cycle4 tau
-- statement:
--   The Plan construction uses the cycle4 tau property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/SmallGraphs.lean#L88-L92
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/SmallGraphs.lean#L88-L92

module
public import Definitions.Def_SizeRamsey_FiniteChecks
public import Definitions.Def_SizeRamsey_SmallGraphs
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v

theorem SizeRamsey.Plan.cycle4_tau : tau4 (SimpleGraph.cycleGraph 4) = 1 ∧
    PrescribedOptimal (SimpleGraph.cycleGraph 4) := by sorry
