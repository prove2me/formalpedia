-- Prove2me | Theorems.Thm_SmallRatio_along_euclid
-- name    : SmallRatio.along_euclid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:25:31.034933+00:00
-- url     : https://prove2.me/theorems/e35f66d8-b685-4cde-9d75-0fe6fa9995d2
-- title:
--   Small Ratio: along euclid
-- statement:
--   **Dedekind sums along Euclid's algorithm** (manuscript, Lemma 5.12):
--   `12 s(h,k) = ∑_{j=1}^n (-1)^{j+1} k/(r_j q_{j-1}) + E` with `|E| ≤ 4n`.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/Solution.lean#L54-L57
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/Solution.lean#L54-L57

module
public import Definitions.Def_SmallRatio
public import Definitions.Def_SmallRatios_Solution
set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset

theorem SmallRatio.along_euclid {k h : ℕ} (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h) :
    |12 * dedekindSum h k - ∑ i ∈ Icc 1 (steps k h),
        (-1) ^ (i + 1) * ((k : ℚ) / ((rem k h i : ℚ) * den k h i))| ≤ 4 * steps k h := by sorry
