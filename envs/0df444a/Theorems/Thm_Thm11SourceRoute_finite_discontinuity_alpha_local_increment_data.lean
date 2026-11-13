-- Prove2me | Theorems.Thm_Thm11SourceRoute_finite_discontinuity_alpha_local_increment_data
-- name    : Thm11SourceRoute.finite_discontinuity_alpha_local_increment_data
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:03:27.881208+00:00
-- url     : https://prove2.me/theorems/0f0e8ead-31e7-4463-a6ad-2b91d1a6ed1e
-- title:
--   ProbabilityTheory_chapter_01_thm_1_1_oscillation_basic_F004: Thm11SourceRoute.finite_discontinuity_alpha_local_increment_data
-- statement:
--   Source theorem `Thm11SourceRoute.finite_discontinuity_alpha_local_increment_data` from `ProbabilityTheory.chapter_01.thm_1_1_oscillation_basic`. The formal Lean declaration specifies its proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_oscillation_basic.lean

import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_basic_F000
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep
open Finset BigOperators
open Set Topology
noncomputable section
namespace Thm11SourceRoute

theorem finite_discontinuity_alpha_local_increment_data
    {f α : ℝ → ℝ} {a b eps : ℝ}
    (hDiscFinite : (discontinuitySetOn f a b).Finite)
    (hαCont :
      ∀ ⦃x : ℝ⦄, x ∈ discontinuitySetOn f a b → ContinuousAt α x)
    (heps : 0 < eps) :
    ∃ S : Finset ℝ,
      (∀ x : ℝ, x ∈ S ↔ x ∈ discontinuitySetOn f a b) ∧
      ∃ rho : ℝ → ℝ,
        (∀ c : ℝ, c ∈ S → 0 < rho c) ∧
        (∑ c ∈ S, (α (c + rho c) - α (c - rho c))) < eps := by
  sorry
end Thm11SourceRoute
end
