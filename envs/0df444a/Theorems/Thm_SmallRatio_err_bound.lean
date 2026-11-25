-- Prove2me | Theorems.Thm_SmallRatio_err_bound
-- name    : SmallRatio.err_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T21:21:34.606873+00:00
-- url     : https://prove2.me/theorems/80ade3c1-0ee5-426d-bf55-d9fb4ccff06c
-- title:
--   Small Ratio: err bound
-- statement:
--   The Small Ratio construction uses the err bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/AlongEuclid.lean#L101-L130
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/AlongEuclid.lean#L101-L130

module
public import Definitions.Def_SmallRatio_Reciprocity
public import Definitions.Def_SmallRatio_Euclid
public import Definitions.Def_SmallRatio_AlongEuclid
set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {k h : ℕ} (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h)
include hh hhk hc

theorem SmallRatio.err_bound {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ steps k h) :
    |(-(den k h (i - 1) : ℚ) / den k h i + (rem k h i : ℚ) / rem k h (i - 1)
        + 1 / ((rem k h i : ℚ) * rem k h (i - 1)) - 3)| ≤ 4 := by sorry
