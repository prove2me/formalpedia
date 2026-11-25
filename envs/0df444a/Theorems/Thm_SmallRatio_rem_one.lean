-- Prove2me | Theorems.Thm_SmallRatio_rem_one
-- name    : SmallRatio.rem_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:17:35.581169+00:00
-- url     : https://prove2.me/theorems/fd41588d-fe34-4a0b-9404-46ea72dfdaf4
-- title:
--   Small Ratio: rem one
-- statement:
--   The Small Ratio construction uses the rem one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L26-L26
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L26-L26

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Euclid
set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {k h : ℕ}

theorem SmallRatio.rem_one : rem k h 1 = h := by sorry

attribute [defeq] SmallRatio.rem_one
