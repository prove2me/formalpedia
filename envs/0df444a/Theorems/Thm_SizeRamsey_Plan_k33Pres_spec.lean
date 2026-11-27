-- Prove2me | Theorems.Thm_SizeRamsey_Plan_k33Pres_spec
-- name    : SizeRamsey.Plan.k33Pres_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:23:15.389016+00:00
-- url     : https://prove2.me/theorems/8345b7e7-64ae-4d55-a95b-d35bdc8fc2dd
-- title:
--   Plan: k33 Pres spec
-- statement:
--   The Plan construction uses the k33 Pres spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/SmallGraphs.lean#L56-L58
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/SmallGraphs.lean#L56-L58

module
public import Definitions.Def_SizeRamsey_FiniteChecks
public import Definitions.Def_SizeRamsey_SmallGraphs
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v

theorem SizeRamsey.Plan.k33Pres_spec : ∀ v, v ∈ k33Pres v ∧ (k33Pres v).card = 2 ∧
    QTrans k33MinusEdge (k33Pres v) := by sorry
