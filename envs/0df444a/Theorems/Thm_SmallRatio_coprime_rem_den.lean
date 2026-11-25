-- Prove2me | Theorems.Thm_SmallRatio_coprime_rem_den
-- name    : SmallRatio.coprime_rem_den
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:22:04.739371+00:00
-- url     : https://prove2.me/theorems/6348193b-6e11-4db4-8e16-afd9f629fc2d
-- title:
--   Small Ratio: coprime rem den
-- statement:
--   For prime `p` the pairs `(r_j, Q_j)` are coprime.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Main.lean#L32-L49
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Main.lean#L32-L49

module
public import Definitions.Def_SmallRatio_AlongEuclid
public import Definitions.Def_SmallRatio_Legendre
public import Definitions.Def_SmallRatio_Main
set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {p h : ℕ} (hp : p.Prime) (hh : 0 < h) (hhp : h < p)
include hp hh hhp

theorem SmallRatio.coprime_rem_den {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ steps p h) :
    Nat.Coprime (rem p h j) (den p h j) := by sorry
