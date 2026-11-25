-- Prove2me | Theorems.Thm_SmallRatio_den_add_two
-- name    : SmallRatio.den_add_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:17:54.049523+00:00
-- url     : https://prove2.me/theorems/dcba0d4b-abe4-4239-8658-7ce8061423c5
-- title:
--   Small Ratio: den add two
-- statement:
--   The Small Ratio construction uses the den add two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L30-L31
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L30-L31

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Euclid
set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {k h : ℕ}

theorem SmallRatio.den_add_two (j : ℕ) :
    den k h (j + 2) = rem k h j / rem k h (j + 1) * den k h (j + 1) + den k h j := by sorry
