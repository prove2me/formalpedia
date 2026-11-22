-- Prove2me | Theorems.Thm_P2M_BooleanIsoperimetry_HIncrement_eq_min__d487d18fa7b9
-- name    : P2M_BooleanIsoperimetry_HIncrement_eq_min__d487d18fa7b9
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:49.595822+00:00
-- url     : https://prove2.me/theorems/cd073ddf-1c40-4df1-bbac-f1ef4a734de9
-- title:
--   P2 M Boolean Isoperimetry HIncrement eq min  d487d18fa7b9: P2 M Boolean Isoperimetry HIncrement eq min  d487d18fa7b9
-- statement:
--   **Exact Macaulay increment profile (minimum-coordinate form).**
--   The `p`-th first difference of the closed-neighbourhood profile `H` equals the
--   smallest active coordinate of the (unique) rank-`p` vertex `w`.  Equivalently,
--   the number of `gShift`-preimages of `w` is `w.min'`.
--
--   This is the exact Kruskal–Katona/Macaulay layer-increment value, upgrading the
--   lower bound `HIncrement_lower` (`n - p ≤ HIncrement n p`, via
--   `rank_add_min_ge`) to a closed form.  It is reusable, non-circular `H`-increment
--   theory: it mentions only `H`, `rank`, `gShift`, and `Finset.min'`, and sits well
--   below the cascade/Macaulay-window leaves in the dependency order.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L159-L184
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L159-L184

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry

theorem P2M_BooleanIsoperimetry_HIncrement_eq_min__d487d18fa7b9 {n : ℕ} (p : ℕ) (w : Cube n) (hw : rank w = p) (hne : w.Nonempty) :
    HIncrement n p = (w.min' hne : ℕ) := by sorry

alias «BooleanIsoperimetry».«HIncrement_eq_min'» := P2M_BooleanIsoperimetry_HIncrement_eq_min__d487d18fa7b9
