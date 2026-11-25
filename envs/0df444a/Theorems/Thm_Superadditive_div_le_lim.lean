-- Prove2me | Theorems.Thm_Superadditive_div_le_lim
-- name    : Superadditive.div_le_lim
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:26:11.537731+00:00
-- url     : https://prove2.me/theorems/db9a9adf-8b45-5168-9719-b49fe5b37f02
-- title:
--   Superadditive: div le lim
-- statement:
--   Every `u n / n` with `n ≠ 0` is bounded by `Superadditive.lim u`.
--
--   Source: https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Superadditive.lean#L126-L129
-- source:
--   https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Superadditive.lean#L126-L129

module
public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_Fekete_Superadditive
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter Set
open scoped Topology
open Superadditive
variable {u : ℕ → ℝ} (h : Superadditive u)

theorem Superadditive.div_le_lim (hbdd : BddAbove (range fun n ↦ u n / n)) {n : ℕ} (hn : n ≠ 0) :
    u n / n ≤ Superadditive.lim u := by sorry
