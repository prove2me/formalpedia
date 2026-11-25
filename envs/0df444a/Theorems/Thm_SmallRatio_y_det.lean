-- Prove2me | Theorems.Thm_SmallRatio_y_det
-- name    : SmallRatio.y_det
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T21:21:31.495064+00:00
-- url     : https://prove2.me/theorems/5a0775f8-26fb-5505-a094-a7f238f056b5
-- title:
--   Small Ratio: y det
-- statement:
--   `r_j y_{j+1} - r_{j+1} y_j = (-1)^j k`.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Legendre.lean#L41-L48
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Legendre.lean#L41-L48

module
public import Definitions.Def_SmallRatio_Euclid
public import Definitions.Def_SmallRatio_Legendre
set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {k h : ℕ} (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h)
include hh hhk hc

theorem SmallRatio.y_det {j : ℕ} (hj : j ≤ steps k h) :
    (rem k h j : ℤ) * ((-1) ^ (j + 2) * den k h (j + 1)) -
      (rem k h (j + 1) : ℤ) * ((-1) ^ (j + 1) * den k h j) = (-1) ^ j * k := by sorry
