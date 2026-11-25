-- Prove2me | Theorems.Thm_SmallRatio_small_ratio_subgroup
-- name    : SmallRatio.small_ratio_subgroup
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T21:25:51.348906+00:00
-- url     : https://prove2.me/theorems/966bbb21-8a05-5605-9532-991f240b70c6
-- title:
--   Small Ratio: small ratio subgroup
-- statement:
--   **The small-ratio formula** (manuscript, Theorem 5.14, Dedekind-sum form). For every set `H` of
--   residues modulo a prime `p`, in particular every subgroup of odd order:
--   `|12 ∑_{h ∈ H} s(h,p) - p S_H(p)| ≤ |H| (12 log₂ p + 6)`.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/Solution.lean#L92-L95
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/Solution.lean#L92-L95

module
public import Definitions.Def_SmallRatio
public import Definitions.Def_SmallRatios_Solution
set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset

theorem SmallRatio.small_ratio_subgroup {p : ℕ} (hp : p.Prime) (H : Finset (ZMod p)) :
    |12 * ∑ x ∈ H, dedekindSum x.val p - p * subgroupSmallRatio p H| ≤
      H.card * (12 * Nat.log 2 p + 6) := by sorry
