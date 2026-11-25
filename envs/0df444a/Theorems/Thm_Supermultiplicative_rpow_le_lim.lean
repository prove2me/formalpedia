-- Prove2me | Theorems.Thm_Supermultiplicative_rpow_le_lim
-- name    : Supermultiplicative.rpow_le_lim
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:26:34.386538+00:00
-- url     : https://prove2.me/theorems/e0b2db55-afd2-501e-b506-03058f86e335
-- title:
--   Supermultiplicative: rpow le lim
-- statement:
--   Every `u n ^ (1 / n)` with `n ≠ 0` is bounded by `Supermultiplicative.lim u`.
--
--   Source: https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Superadditive.lean#L207-L210
-- source:
--   https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Superadditive.lean#L207-L210

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
open Supermultiplicative
variable {u : ℕ → ℝ}

theorem Supermultiplicative.rpow_le_lim (hbdd : BddAbove (range fun n ↦ u n ^ (n : ℝ)⁻¹)) {n : ℕ} (hn : n ≠ 0) :
    u n ^ (n : ℝ)⁻¹ ≤ Supermultiplicative.lim u := by sorry
