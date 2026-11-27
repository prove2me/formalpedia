-- Prove2me | Theorems.Thm_SizeRamsey_Plan_k33MinusEdge_edgeCount
-- name    : SizeRamsey.Plan.k33MinusEdge_edgeCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:22:58.023948+00:00
-- url     : https://prove2.me/theorems/0a64d152-4cb3-4737-a5e2-f5a2f9f79c63
-- title:
--   Plan: k33 Minus Edge edge Count
-- statement:
--   The Plan construction uses the k33 Minus Edge edge Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/SmallGraphs.lean#L32-L33
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/SmallGraphs.lean#L32-L33

module
public import Definitions.Def_SizeRamsey_FiniteChecks
public import Definitions.Def_SizeRamsey_SmallGraphs
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v

theorem SizeRamsey.Plan.k33MinusEdge_edgeCount : edgeCount k33MinusEdge = 8 := by sorry
