-- Prove2me | Theorems.Thm_Superadditive_tendsto_div_atTop
-- name    : Superadditive.tendsto_div_atTop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:26:15.332841+00:00
-- url     : https://prove2.me/theorems/4372bb87-b53d-5d97-be71-4203431622e9
-- title:
--   Superadditive: tendsto div at Top
-- statement:
--   **Fekete's lemma, superadditive form, unbounded case**: if `u n / n` is not bounded above,
--   then `u n / n → ∞`.
--
--   Source: https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Superadditive.lean#L155-L161
-- source:
--   https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Superadditive.lean#L155-L161

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

theorem Superadditive.tendsto_div_atTop (hbdd : ¬ BddAbove (range fun n ↦ u n / n)) :
    Tendsto (fun n ↦ u n / n) atTop atTop := by sorry
