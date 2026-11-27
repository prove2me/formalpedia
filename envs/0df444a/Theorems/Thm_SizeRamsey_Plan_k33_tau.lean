-- Prove2me | Theorems.Thm_SizeRamsey_Plan_k33_tau
-- name    : SizeRamsey.Plan.k33_tau
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:23:30.864882+00:00
-- url     : https://prove2.me/theorems/2bf5a31f-241e-4ed3-9853-54064f20763d
-- title:
--   Plan: k33 tau
-- statement:
--   The Plan construction uses the k33 tau property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/SmallGraphs.lean#L98-L100
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/SmallGraphs.lean#L98-L100

module
public import Definitions.Def_SizeRamsey_FiniteChecks
public import Definitions.Def_SizeRamsey_SmallGraphs
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v

theorem SizeRamsey.Plan.k33_tau : tau4 k33MinusEdge = 2 ∧ PrescribedOptimal k33MinusEdge := by sorry
