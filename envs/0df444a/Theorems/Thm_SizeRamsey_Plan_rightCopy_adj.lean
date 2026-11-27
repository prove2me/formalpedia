-- Prove2me | Theorems.Thm_SizeRamsey_Plan_rightCopy_adj
-- name    : SizeRamsey.Plan.rightCopy_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:25:27.716805+00:00
-- url     : https://prove2.me/theorems/36704421-1e05-42b5-adf3-a0332e3a512f
-- title:
--   Plan: right Copy adj
-- statement:
--   The Plan construction uses the right Copy adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Upper.lean#L108-L111
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Upper.lean#L108-L111

module
public import Definitions.Def_SizeRamsey_AInterface
public import Definitions.Def_SizeRamsey_Upper
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan

theorem SizeRamsey.Plan.rightCopy_adj (i j : Fin 6) :
    F17.Adj (rightCopy i) (rightCopy j) ↔
      k33MinusEdge.Adj i j := by sorry
