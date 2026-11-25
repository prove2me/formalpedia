-- Prove2me | Theorems.Thm_SmallRatio_small_ratio
-- name    : SmallRatio.small_ratio
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T21:25:16.043269+00:00
-- url     : https://prove2.me/theorems/3a940169-9e8b-5340-ba43-4aa3a53ee31e
-- title:
--   Small Ratio: small ratio
-- statement:
--   **The small-ratio formula for one residue**, with the number of steps:
--   `|12 s(h,p) - p ∑ ([hv ≡ u] - [hv ≡ -u])/(uv)| ≤ 6n`, the sum over coprime `u, v ≥ 1` with `uv < p/2`.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/Solution.lean#L74-L76
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/Solution.lean#L74-L76

module
public import Definitions.Def_SmallRatio
public import Definitions.Def_SmallRatios_Solution
set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset

theorem SmallRatio.small_ratio {p h : ℕ} (hp : p.Prime) (hh : 0 < h) (hhp : h < p) :
    |12 * dedekindSum h p - p * smallRatioSum p h| ≤ 6 * steps p h := by sorry
