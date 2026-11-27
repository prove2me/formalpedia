-- Prove2me | Theorems.Thm_SizeRamsey_Plan_copies_disjoint
-- name    : SizeRamsey.Plan.copies_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:25:06.405449+00:00
-- url     : https://prove2.me/theorems/3bcd403f-fff9-49ac-91ba-08970838679f
-- title:
--   Plan: copies disjoint
-- statement:
--   The Plan construction uses the copies disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Upper.lean#L96-L101
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Upper.lean#L96-L101

module
public import Definitions.Def_SizeRamsey_AInterface
public import Definitions.Def_SizeRamsey_Upper
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan

theorem SizeRamsey.Plan.copies_disjoint (i j : Fin 6) :
    leftCopy i ≠ rightCopy j := by sorry
