-- Prove2me | Theorems.Thm_SmallRatio_euclid_terminates
-- name    : SmallRatio.euclid_terminates
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T21:24:45.894804+00:00
-- url     : https://prove2.me/theorems/f5df735e-fc7c-4ae0-8363-6ed011e1a129
-- title:
--   Small Ratio: euclid terminates
-- statement:
--   **Euclid's algorithm.** For `0 < h < k` coprime, with `r_j = rem k h j` and `n = steps k h`:
--   `r_n = 1`, `r_j ≥ 2` for `j < n`, and `r` decreases strictly on `[0, n]`.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/Solution.lean#L30-L34
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/Solution.lean#L30-L34

module
public import Definitions.Def_SmallRatio
public import Definitions.Def_SmallRatios_Solution
set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset

theorem SmallRatio.euclid_terminates {k h : ℕ} (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h) :
    rem k h (steps k h) = 1 ∧ (∀ j < steps k h, 2 ≤ rem k h j) ∧
      ∀ i j, i < j → j ≤ steps k h → rem k h j < rem k h i := by sorry
