-- Prove2me | Theorems.Thm_SmallRatio_den_congr
-- name    : SmallRatio.den_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:19:46.742298+00:00
-- url     : https://prove2.me/theorems/dd3c569c-1b93-454e-85ed-62c1cc2b2197
-- title:
--   Small Ratio: den congr
-- statement:
--   `h Q_j ≡ (-1)^{j+1} r_j (mod k)` for every `j`.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L145-L168
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L145-L168

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
omit hh hhk hc

theorem SmallRatio.den_congr (j : ℕ) :
    (k : ℤ) ∣ (h : ℤ) * den k h j - (-1) ^ (j + 1) * rem k h j := by sorry
