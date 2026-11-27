-- Prove2me | Theorems.Thm_SizeRamsey_Plan_rightCopy_injective
-- name    : SizeRamsey.Plan.rightCopy_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:25:02.750095+00:00
-- url     : https://prove2.me/theorems/a17ca27f-81f5-5ba8-b951-f99764efed4f
-- title:
--   Plan: right Copy injective
-- statement:
--   The Plan construction uses the right Copy injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Upper.lean#L88-L94
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Upper.lean#L88-L94

module
public import Definitions.Def_SizeRamsey_AInterface
public import Definitions.Def_SizeRamsey_Upper
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan

theorem SizeRamsey.Plan.rightCopy_injective :
    Function.Injective rightCopy := by sorry
