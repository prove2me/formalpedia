-- Prove2me | Theorems.Thm_SmallRatio_rem_zero
-- name    : SmallRatio.rem_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:17:32.15896+00:00
-- url     : https://prove2.me/theorems/917ad994-b1ba-4997-ac26-2a0304fe5e16
-- title:
--   Small Ratio: rem zero
-- statement:
--   The Small Ratio construction uses the rem zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L25-L25
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L25-L25

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Euclid
set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {k h : ℕ}

theorem SmallRatio.rem_zero : rem k h 0 = k := by sorry

attribute [defeq] SmallRatio.rem_zero
