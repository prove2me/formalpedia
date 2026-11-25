-- Prove2me | Theorems.Thm_SmallRatio_recipTerm_eq
-- name    : SmallRatio.recipTerm_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T21:21:19.624908+00:00
-- url     : https://prove2.me/theorems/2a5a354a-20d7-41f6-8f0e-46bff291e2b4
-- title:
--   Small Ratio: recip Term eq
-- statement:
--   The error term `e_j = r_{j-1}/r_j - k/(r_j Q_j) + r_j/r_{j-1} + 1/(r_j r_{j-1}) - 3`.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/AlongEuclid.lean#L83-L99
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/AlongEuclid.lean#L83-L99

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

theorem SmallRatio.recipTerm_eq {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ steps k h) :
    recipTerm k h i = (k : ℚ) / ((rem k h i : ℚ) * den k h i) +
      (-(den k h (i - 1) : ℚ) / den k h i + (rem k h i : ℚ) / rem k h (i - 1)
        + 1 / ((rem k h i : ℚ) * rem k h (i - 1)) - 3) := by sorry
