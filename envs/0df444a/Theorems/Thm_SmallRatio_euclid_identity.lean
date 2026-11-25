-- Prove2me | Theorems.Thm_SmallRatio_euclid_identity
-- name    : SmallRatio.euclid_identity
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T21:24:35.19711+00:00
-- url     : https://prove2.me/theorems/83f00428-8778-55f8-909a-5c4e14c8d0a6
-- title:
--   Small Ratio: euclid identity
-- statement:
--   **The identity `r_{j-1} q_{j-1} + r_j q_{j-2} = k`** of the manuscript, with `den k h j = q_{j-1}`:
--   `r_j Q_{j+1} + r_{j+1} Q_j = k` for `j ≤ n`.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/Solution.lean#L38-L40
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/Solution.lean#L38-L40

module
public import Definitions.Def_SmallRatio
public import Definitions.Def_SmallRatios_Solution
set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset

theorem SmallRatio.euclid_identity {k h : ℕ} (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h) :
    ∀ j ≤ steps k h, rem k h j * den k h (j + 1) + rem k h (j + 1) * den k h j = k := by sorry
