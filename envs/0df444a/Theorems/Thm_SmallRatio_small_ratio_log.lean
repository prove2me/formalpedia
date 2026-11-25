-- Prove2me | Theorems.Thm_SmallRatio_small_ratio_log
-- name    : SmallRatio.small_ratio_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:25:33.511025+00:00
-- url     : https://prove2.me/theorems/ba432795-813a-587b-866f-d9ad9870082b
-- title:
--   Small Ratio: small ratio log
-- statement:
--   **The small-ratio formula for one residue:**
--   `|12 s(h,p) - p ∑ ([hv ≡ u] - [hv ≡ -u])/(uv)| ≤ 12 log₂ p + 6`.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/Solution.lean#L80-L82
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/Solution.lean#L80-L82

module
public import Definitions.Def_SmallRatio
public import Definitions.Def_SmallRatios_Solution
set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset

theorem SmallRatio.small_ratio_log {p h : ℕ} (hp : p.Prime) (hh : 0 < h) (hhp : h < p) :
    |12 * dedekindSum h p - p * smallRatioSum p h| ≤ 12 * Nat.log 2 p + 6 := by sorry
