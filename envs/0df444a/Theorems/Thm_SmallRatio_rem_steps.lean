-- Prove2me | Theorems.Thm_SmallRatio_rem_steps
-- name    : SmallRatio.rem_steps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:18:35.221264+00:00
-- url     : https://prove2.me/theorems/f80c557f-1107-4303-84cf-69210c6b0dc3
-- title:
--   Small Ratio: rem steps
-- statement:
--   The Small Ratio construction uses the rem steps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L84-L93
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L84-L93

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Euclid
set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {k h : ℕ}
variable (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h)
include hh hhk hc

theorem SmallRatio.rem_steps : rem k h (steps k h) = 1 := by sorry
