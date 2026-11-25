-- Prove2me | Theorems.Thm_SmallRatio_rem_le_of_ge_two
-- name    : SmallRatio.rem_le_of_ge_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:19:36.538808+00:00
-- url     : https://prove2.me/theorems/e9692f46-2a2b-4370-b06e-eda543af500f
-- title:
--   Small Ratio: rem le of ge two
-- statement:
--   While the remainders stay `≥ 2`, they decrease from `r_1 = h`.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L43-L50
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L43-L50

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Euclid
set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {k h : ℕ}

theorem SmallRatio.rem_le_of_ge_two (j : ℕ) (hge : ∀ i ≤ j + 1, 2 ≤ rem k h i) : rem k h (j + 1) + j ≤ h := by sorry
