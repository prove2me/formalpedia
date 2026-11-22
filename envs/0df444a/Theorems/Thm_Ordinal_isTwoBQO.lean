-- Prove2me | Theorems.Thm_Ordinal_isTwoBQO
-- name    : Ordinal.isTwoBQO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:37.284211+00:00
-- url     : https://prove2.me/theorems/11c83abf-9db6-4d5e-a0dd-d6211d3aa3ef
-- title:
--   Ordinal: is Two BQO
-- statement:
--   **Ordinals are 2-BQO** with respect to `≤`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/TwoBQO.lean#L163-L164
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/TwoBQO.lean#L163-L164

module
public import Mathlib.SetTheory.Ordinal.Basic
public import Definitions.Def_LeanPool_NashWilliams_Order_WellQuasiOrder_Regular
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Ramsey_Infinite
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_NashWilliams_Order_TwoBQO
set_option autoImplicit true
@[expose] public section
public section
open Set Preorder
noncomputable section

theorem Ordinal.isTwoBQO : TwoBQO (α := Ordinal) (· ≤ ·) := by sorry
