-- Prove2me | Theorems.Thm_SmallRatio_dedekind_reciprocity
-- name    : SmallRatio.dedekind_reciprocity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:15:26.413259+00:00
-- url     : https://prove2.me/theorems/759c04b4-f86f-4427-b0b0-864602e7bcce
-- title:
--   Small Ratio: dedekind reciprocity
-- statement:
--   **Dedekind reciprocity.**
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Reciprocity.lean#L210-L294
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Reciprocity.lean#L210-L294

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Reciprocity
set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset

theorem SmallRatio.dedekind_reciprocity (h k : ℕ) (hh : 0 < h) (hk : 0 < k) (hc : Nat.Coprime h k) :
    dedekindSum h k + dedekindSum k h =
      ((h : ℚ) / k + (k : ℚ) / h + 1 / ((h : ℚ) * k)) / 12 - 1 / 4 := by sorry
