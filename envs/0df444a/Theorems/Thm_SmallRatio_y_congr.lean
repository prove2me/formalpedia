-- Prove2me | Theorems.Thm_SmallRatio_y_congr
-- name    : SmallRatio.y_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:21:24.184933+00:00
-- url     : https://prove2.me/theorems/f05d1ac6-828e-5a88-911d-30f9401c3480
-- title:
--   Small Ratio: y congr
-- statement:
--   `h y_j ≡ r_j (mod k)` with `y_j = (-1)^{j+1} Q_j`.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Legendre.lean#L31-L38
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Legendre.lean#L31-L38

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
omit hh hhk hc

theorem SmallRatio.y_congr (j : ℕ) :
    (k : ℤ) ∣ (h : ℤ) * ((-1) ^ (j + 1) * den k h j) - rem k h j := by sorry
