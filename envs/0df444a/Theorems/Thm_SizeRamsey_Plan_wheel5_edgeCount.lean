-- Prove2me | Theorems.Thm_SizeRamsey_Plan_wheel5_edgeCount
-- name    : SizeRamsey.Plan.wheel5_edgeCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:22:57.554939+00:00
-- url     : https://prove2.me/theorems/299ceeaf-5e9d-43ae-92ed-17067f45d67b
-- title:
--   Plan: wheel5 edge Count
-- statement:
--   The Plan construction uses the wheel5 edge Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/SmallGraphs.lean#L29-L30
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/SmallGraphs.lean#L29-L30

module
public import Definitions.Def_SizeRamsey_FiniteChecks
public import Definitions.Def_SizeRamsey_SmallGraphs
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v

theorem SizeRamsey.Plan.wheel5_edgeCount : edgeCount wheel5 = 8 := by sorry
