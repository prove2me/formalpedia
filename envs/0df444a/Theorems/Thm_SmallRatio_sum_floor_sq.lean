-- Prove2me | Theorems.Thm_SmallRatio_sum_floor_sq
-- name    : SmallRatio.sum_floor_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:14:56.693128+00:00
-- url     : https://prove2.me/theorems/b173259e-d2f7-567f-a737-67474f71e53a
-- title:
--   Small Ratio: sum floor sq
-- statement:
--   Lattice points under `y = hx/k`: `∑_{r<k} ⌊hr/k⌋² = ∑_{0<j<h} (2j-1)(k-1-⌊kj/h⌋)`.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Reciprocity.lean#L139-L183
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Reciprocity.lean#L139-L183

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Reciprocity
set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset

theorem SmallRatio.sum_floor_sq (h k : ℕ) (hh : 0 < h) (hk : 0 < k) (hc : Nat.Coprime h k) :
    ∑ r ∈ range k, ((h * r / k : ℕ) : ℤ) ^ 2 =
      ∑ j ∈ Ico 1 h, (2 * (j : ℤ) - 1) * ((k : ℤ) - 1 - ((k * j / h : ℕ) : ℤ)) := by sorry
