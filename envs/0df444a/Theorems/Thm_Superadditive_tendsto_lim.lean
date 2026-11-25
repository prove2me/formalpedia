-- Prove2me | Theorems.Thm_Superadditive_tendsto_lim
-- name    : Superadditive.tendsto_lim
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:26:14.738633+00:00
-- url     : https://prove2.me/theorems/183c623a-bce9-544d-baa7-834a61960ceb
-- title:
--   Superadditive: tendsto lim
-- statement:
--   **Fekete's lemma, superadditive form**: if `u n / n` is bounded above, it converges to its
--   supremum over `n ≥ 1`.
--
--   Source: https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Superadditive.lean#L134-L150
-- source:
--   https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Superadditive.lean#L134-L150

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
include h

theorem Superadditive.tendsto_lim (hbdd : BddAbove (range fun n ↦ u n / n)) :
    Tendsto (fun n ↦ u n / n) atTop (𝓝 (Superadditive.lim u)) := by sorry
