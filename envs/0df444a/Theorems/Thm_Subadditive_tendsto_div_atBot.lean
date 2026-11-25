-- Prove2me | Theorems.Thm_Subadditive_tendsto_div_atBot
-- name    : Subadditive.tendsto_div_atBot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:26:27.18274+00:00
-- url     : https://prove2.me/theorems/f5972931-b4cf-448f-a5fe-3c8d63869c0e
-- title:
--   Subadditive: tendsto div at Bot
-- statement:
--   **Fekete's lemma, unbounded case.** If `u` is subadditive and `u n / n` is not bounded below,
--   then `u n / n → -∞`. Together with `Subadditive.tendsto_lim` this says that `u n / n` always
--   converges in `[-∞, ∞)`.
--
--   Source: https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Superadditive.lean#L63-L89
-- source:
--   https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Superadditive.lean#L63-L89

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

theorem Subadditive.tendsto_div_atBot {u : ℕ → ℝ} (h : Subadditive u)
    (hbdd : ¬ BddBelow (range fun n ↦ u n / n)) :
    Tendsto (fun n ↦ u n / n) atTop atBot := by sorry
