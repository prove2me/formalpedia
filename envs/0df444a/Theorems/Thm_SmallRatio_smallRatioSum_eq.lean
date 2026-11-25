-- Prove2me | Theorems.Thm_SmallRatio_smallRatioSum_eq
-- name    : SmallRatio.smallRatioSum_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T21:21:39.625206+00:00
-- url     : https://prove2.me/theorems/9c549a28-1c0d-5771-950e-89d8d2e22f46
-- title:
--   Small Ratio: small Ratio Sum eq
-- statement:
--   The small-ratio sum as a sum over the steps of the algorithm.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Main.lean#L52-L138
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Main.lean#L52-L138

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

theorem SmallRatio.smallRatioSum_eq :
    smallRatioSum p h = ∑ i ∈ Icc 1 (steps p h),
      if 2 * rem p h i * den p h i < p then
        (-1) ^ (i + 1) / ((rem p h i : ℚ) * den p h i) else 0 := by sorry
