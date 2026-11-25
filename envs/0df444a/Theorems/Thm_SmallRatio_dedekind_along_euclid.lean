-- Prove2me | Theorems.Thm_SmallRatio_dedekind_along_euclid
-- name    : SmallRatio.dedekind_along_euclid
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T21:21:37.154926+00:00
-- url     : https://prove2.me/theorems/4c380a13-ad27-4183-9335-ec5c2f049105
-- title:
--   Small Ratio: dedekind along euclid
-- statement:
--   **Dedekind sums along Euclid's algorithm.**
--   `|12 s(h,k) - ∑_{j=1}^n (-1)^{j+1} k/(r_j Q_j)| ≤ 4n`.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/AlongEuclid.lean#L134-L150
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/AlongEuclid.lean#L134-L150

module
public import Definitions.Def_SmallRatio_Reciprocity
public import Definitions.Def_SmallRatio_Euclid
public import Definitions.Def_SmallRatio_AlongEuclid
set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {k h : ℕ} (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h)
include hh hhk hc

theorem SmallRatio.dedekind_along_euclid :
    |12 * dedekindSum h k - ∑ i ∈ Icc 1 (steps k h),
        (-1) ^ (i + 1) * ((k : ℚ) / ((rem k h i : ℚ) * den k h i))| ≤ 4 * steps k h := by sorry
