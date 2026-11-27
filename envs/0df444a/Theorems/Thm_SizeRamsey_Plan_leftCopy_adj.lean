-- Prove2me | Theorems.Thm_SizeRamsey_Plan_leftCopy_adj
-- name    : SizeRamsey.Plan.leftCopy_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:25:09.434798+00:00
-- url     : https://prove2.me/theorems/fef9df0a-de35-4777-b711-4f7fa9a15f6e
-- title:
--   Plan: left Copy adj
-- statement:
--   The Plan construction uses the left Copy adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Upper.lean#L103-L106
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Upper.lean#L103-L106

module
public import Definitions.Def_SizeRamsey_AInterface
public import Definitions.Def_SizeRamsey_Upper
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan

theorem SizeRamsey.Plan.leftCopy_adj (i j : Fin 6) :
    F17.Adj (leftCopy i) (leftCopy j) ↔
      k33MinusEdge.Adj i j := by sorry
