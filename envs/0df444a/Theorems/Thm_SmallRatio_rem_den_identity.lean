-- Prove2me | Theorems.Thm_SmallRatio_rem_den_identity
-- name    : SmallRatio.rem_den_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:19:18.448969+00:00
-- url     : https://prove2.me/theorems/3ef0e5d8-a15d-4d49-864e-62f2e5017c4b
-- title:
--   Small Ratio: rem den identity
-- statement:
--   `r_j Q_{j+1} + r_{j+1} Q_j = k` for `j ≤ n`.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L128-L141
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L128-L141

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

theorem SmallRatio.rem_den_identity {j : ℕ} (hj : j ≤ steps k h) :
    rem k h j * den k h (j + 1) + rem k h (j + 1) * den k h j = k := by sorry
