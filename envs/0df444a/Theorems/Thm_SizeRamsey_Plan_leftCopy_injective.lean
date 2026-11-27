-- Prove2me | Theorems.Thm_SizeRamsey_Plan_leftCopy_injective
-- name    : SizeRamsey.Plan.leftCopy_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:24:59.920721+00:00
-- url     : https://prove2.me/theorems/b5222bb5-1e13-49b6-b93b-0d92d1daa336
-- title:
--   Plan: left Copy injective
-- statement:
--   The Plan construction uses the left Copy injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Upper.lean#L82-L86
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Upper.lean#L82-L86

module
public import Definitions.Def_SizeRamsey_AInterface
public import Definitions.Def_SizeRamsey_Upper
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan

theorem SizeRamsey.Plan.leftCopy_injective :
    Function.Injective leftCopy := by sorry
