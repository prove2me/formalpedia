-- Prove2me | Theorems.Thm_SmallRatio_pairs_coprime
-- name    : SmallRatio.pairs_coprime
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T21:26:08.765416+00:00
-- url     : https://prove2.me/theorems/0db29af7-8b92-484b-a948-d5ed87e9cf15
-- title:
--   Small Ratio: pairs coprime
-- statement:
--   For a prime modulus the pairs `(r_j, q_{j-1})`, `1 ≤ j ≤ n`, are coprime.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/Solution.lean#L68-L70
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/Solution.lean#L68-L70

module
public import Definitions.Def_SmallRatio
public import Definitions.Def_SmallRatios_Solution
set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset

theorem SmallRatio.pairs_coprime {p h : ℕ} (hp : p.Prime) (hh : 0 < h) (hhp : h < p) :
    ∀ j, 1 ≤ j → j ≤ steps p h → Nat.Coprime (rem p h j) (den p h j) := by sorry
