-- Prove2me | Theorems.Thm_SizeRamsey_Plan_wheel5_tau
-- name    : SizeRamsey.Plan.wheel5_tau
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:23:31.123056+00:00
-- url     : https://prove2.me/theorems/1888d71f-1d2e-503e-bc44-972eb85cd56d
-- title:
--   Plan: wheel5 tau
-- statement:
--   The Plan construction uses the wheel5 tau property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/SmallGraphs.lean#L94-L96
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/SmallGraphs.lean#L94-L96

module
public import Definitions.Def_SizeRamsey_FiniteChecks
public import Definitions.Def_SizeRamsey_SmallGraphs
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v

theorem SizeRamsey.Plan.wheel5_tau : tau4 wheel5 = 2 ∧ PrescribedOptimal wheel5 := by sorry
