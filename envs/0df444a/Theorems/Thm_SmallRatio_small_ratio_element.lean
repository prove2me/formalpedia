-- Prove2me | Theorems.Thm_SmallRatio_small_ratio_element
-- name    : SmallRatio.small_ratio_element
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:22:06.54119+00:00
-- url     : https://prove2.me/theorems/063e00f1-5309-488a-927b-21cef3a93716
-- title:
--   Small Ratio: small ratio element
-- statement:
--   **The small-ratio formula for one residue**, with `n ≤ 2 log₂ p + 1`.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Main.lean#L178-L186
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Main.lean#L178-L186

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

theorem SmallRatio.small_ratio_element :
    |12 * dedekindSum h p - p * smallRatioSum p h| ≤ 12 * Nat.log 2 p + 6 := by sorry
