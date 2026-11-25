-- Prove2me | Theorems.Thm_SmallRatio_smallRatioSum_zero
-- name    : SmallRatio.smallRatioSum_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:22:25.733798+00:00
-- url     : https://prove2.me/theorems/ece55044-b286-4df8-ab58-687f6b016c32
-- title:
--   Small Ratio: small Ratio Sum zero
-- statement:
--   The Small Ratio construction uses the small Ratio Sum zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Subgroup.lean#L25-L46
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Subgroup.lean#L25-L46

module
public import Definitions.Def_SmallRatio_Main
public import Definitions.Def_SmallRatio_Subgroup
set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {p : ℕ}

theorem SmallRatio.smallRatioSum_zero (hp : p.Prime) : smallRatioSum p 0 = 0 := by sorry
