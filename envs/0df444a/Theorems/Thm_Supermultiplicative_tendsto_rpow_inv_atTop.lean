-- Prove2me | Theorems.Thm_Supermultiplicative_tendsto_rpow_inv_atTop
-- name    : Supermultiplicative.tendsto_rpow_inv_atTop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:26:37.900922+00:00
-- url     : https://prove2.me/theorems/7c5030ac-7969-5128-abcf-cf0e0a9b9128
-- title:
--   Supermultiplicative: tendsto rpow inv at Top
-- statement:
--   **Fekete's lemma, supermultiplicative form, unbounded case.**
--
--   Source: https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Superadditive.lean#L240-L249
-- source:
--   https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Superadditive.lean#L240-L249

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

theorem Supermultiplicative.tendsto_rpow_inv_atTop (h : Supermultiplicative u) (hpos : ∀ n, n ≠ 0 → 0 < u n)
    (hbdd : ¬ BddAbove (range fun n ↦ u n ^ (n : ℝ)⁻¹)) :
    Tendsto (fun n ↦ u n ^ (n : ℝ)⁻¹) atTop atTop := by sorry
