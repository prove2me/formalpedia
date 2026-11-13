-- Prove2me | Theorems.Thm_Thm11SourceRoute_exists_pos_mesh_bound_le_good_and_half_radii
-- name    : Thm11SourceRoute.exists_pos_mesh_bound_le_good_and_half_radii
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T22:58:24.150993+00:00
-- url     : https://prove2.me/theorems/403ed077-7840-4ec4-86e1-6f5614bed45e
-- title:
--   Chapter 1, thm_1_1_bad_cells: Thm11SourceRoute.exists_pos_mesh_bound_le_good_and_half_radii
-- statement:
--   Source theorem `Thm11SourceRoute.exists_pos_mesh_bound_le_good_and_half_radii` from Chapter 1, module `thm_1_1_bad_cells`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_bad_cells.lean

import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep

open Finset BigOperators
open Set Topology

noncomputable section

namespace Thm11SourceRoute

theorem exists_pos_mesh_bound_le_good_and_half_radii
    (S : Finset ℝ) (rho : ℝ → ℝ) {δgood : ℝ}
    (hδgood : 0 < δgood)
    (hrho_pos : ∀ c : ℝ, c ∈ S → 0 < rho c) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δgood ∧
      ∀ c : ℝ, c ∈ S → δ ≤ rho c / 2 := by sorry

end Thm11SourceRoute
