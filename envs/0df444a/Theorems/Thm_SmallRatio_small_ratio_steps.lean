-- Prove2me | Theorems.Thm_SmallRatio_small_ratio_steps
-- name    : SmallRatio.small_ratio_steps
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T21:21:49.198451+00:00
-- url     : https://prove2.me/theorems/e1a2a7c0-1202-57a3-8169-3c1357d183e6
-- title:
--   Small Ratio: small ratio steps
-- statement:
--   **The small-ratio formula for one residue.**
--   `|12 s(h,p) - p ∑ ([hv ≡ u] - [hv ≡ -u])/(uv)| ≤ 6n`.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Main.lean#L142-L175
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Main.lean#L142-L175

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

theorem SmallRatio.small_ratio_steps :
    |12 * dedekindSum h p - p * smallRatioSum p h| ≤ 6 * steps p h := by sorry
