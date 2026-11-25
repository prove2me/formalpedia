-- Prove2me | Theorems.Thm_SmallRatio_reciprocity
-- name    : SmallRatio.reciprocity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:25:03.438192+00:00
-- url     : https://prove2.me/theorems/b6f59027-861e-4655-85a3-65dd8891847a
-- title:
--   Small Ratio: reciprocity
-- statement:
--   **Dedekind reciprocity.** For coprime positive `h`, `k`:
--   `s(h,k) + s(k,h) = (h/k + k/h + 1/(hk))/12 - 1/4`.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/Solution.lean#L23-L26
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/Solution.lean#L23-L26

module
public import Definitions.Def_SmallRatio
public import Definitions.Def_SmallRatios_Solution
set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset

theorem SmallRatio.reciprocity (h k : ℕ) (hh : 0 < h) (hk : 0 < k) (hc : Nat.Coprime h k) :
    dedekindSum h k + dedekindSum k h =
      ((h : ℚ) / k + (k : ℚ) / h + 1 / ((h : ℚ) * k)) / 12 - 1 / 4 := by sorry
