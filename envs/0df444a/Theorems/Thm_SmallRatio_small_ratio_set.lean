-- Prove2me | Theorems.Thm_SmallRatio_small_ratio_set
-- name    : SmallRatio.small_ratio_set
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:23:00.258568+00:00
-- url     : https://prove2.me/theorems/cfee70e6-ef30-5813-9c33-fe8b98e7428f
-- title:
--   Small Ratio: small ratio set
-- statement:
--   **The small-ratio formula over a set of residues.**
--   `|12 ∑_{h ∈ H} s(h,p) - p S_H(p)| ≤ |H| (12 log₂ p + 6)`.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Subgroup.lean#L81-L100
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Subgroup.lean#L81-L100

module
public import Definitions.Def_SmallRatio_Main
public import Definitions.Def_SmallRatio_Subgroup
set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {p : ℕ}

theorem SmallRatio.small_ratio_set (hp : p.Prime) (H : Finset (ZMod p)) :
    |12 * ∑ x ∈ H, dedekindSum x.val p - p * subgroupSmallRatio p H| ≤
      H.card * (12 * Nat.log 2 p + 6) := by sorry
