-- Prove2me | Theorems.Thm_SmallRatio_sum_smallRatioSum
-- name    : SmallRatio.sum_smallRatioSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:22:05.319776+00:00
-- url     : https://prove2.me/theorems/db9de826-59cb-5ec3-b924-ce7d89bc39c4
-- title:
--   Small Ratio: sum small Ratio Sum
-- statement:
--   The Small Ratio construction uses the sum small Ratio Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Subgroup.lean#L48-L77
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Subgroup.lean#L48-L77

module
public import Definitions.Def_SmallRatio_Main
public import Definitions.Def_SmallRatio_Subgroup
set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {p : ℕ}

theorem SmallRatio.sum_smallRatioSum (hp : p.Prime) (H : Finset (ZMod p)) :
    ∑ x ∈ H, smallRatioSum p x.val = subgroupSmallRatio p H := by sorry
