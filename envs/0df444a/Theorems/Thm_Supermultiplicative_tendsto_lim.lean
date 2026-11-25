-- Prove2me | Theorems.Thm_Supermultiplicative_tendsto_lim
-- name    : Supermultiplicative.tendsto_lim
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:26:35.533868+00:00
-- url     : https://prove2.me/theorems/f421cfdc-ff22-5f7a-bc8a-5399f4004e06
-- title:
--   Supermultiplicative: tendsto lim
-- statement:
--   **Fekete's lemma, supermultiplicative form**: if `u n > 0` for `n ≠ 0`, `u` is
--   supermultiplicative and `u n ^ (1 / n)` is bounded above, then it converges to its supremum over
--   `n ≥ 1`.
--
--   Source: https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Superadditive.lean#L215-L237
-- source:
--   https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Superadditive.lean#L215-L237

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

theorem Supermultiplicative.tendsto_lim (h : Supermultiplicative u) (hpos : ∀ n, n ≠ 0 → 0 < u n)
    (hbdd : BddAbove (range fun n ↦ u n ^ (n : ℝ)⁻¹)) :
    Tendsto (fun n ↦ u n ^ (n : ℝ)⁻¹) atTop (𝓝 (Supermultiplicative.lim u)) := by sorry
