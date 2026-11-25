-- Prove2me | Theorems.Thm_SmallRatio_euclid_congruence
-- name    : SmallRatio.euclid_congruence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:25:31.945362+00:00
-- url     : https://prove2.me/theorems/333245ff-3646-4078-9df1-c74db2a69651
-- title:
--   Small Ratio: euclid congruence
-- statement:
--   **The congruence `h q_{j-1} ≡ (-1)^{j+1} r_j (mod k)`**, for every `j`.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/Solution.lean#L43-L45
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/Solution.lean#L43-L45

module
public import Definitions.Def_SmallRatio
public import Definitions.Def_SmallRatios_Solution
set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset

theorem SmallRatio.euclid_congruence (k h j : ℕ) :
    (k : ℤ) ∣ (h : ℤ) * den k h j - (-1) ^ (j + 1) * rem k h j := by sorry
