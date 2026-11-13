-- Prove2me | Theorems.Thm_Thm11SourceRoute_finite_discontinuity_alpha_local_increment_pairwise_data
-- name    : Thm11SourceRoute.finite_discontinuity_alpha_local_increment_pairwise_data
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:03:39.278252+00:00
-- url     : https://prove2.me/theorems/ba5d36b8-4d5d-4703-ade1-decda6a2fd5f
-- title:
--   ProbabilityTheory_chapter_01_thm_1_1_oscillation_basic_F004: Thm11SourceRoute.finite_discontinuity_alpha_local_increment_pairwise_data
-- statement:
--   Source theorem `Thm11SourceRoute.finite_discontinuity_alpha_local_increment_pairwise_data` from `ProbabilityTheory.chapter_01.thm_1_1_oscillation_basic`. The formal Lean declaration specifies its proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_oscillation_basic.lean

import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_basic_F000
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep
open Finset BigOperators
open Set Topology
noncomputable section
namespace Thm11SourceRoute

theorem finite_discontinuity_alpha_local_increment_pairwise_data
    {f α : ℝ → ℝ} {a b eps : ℝ}
    (hα_mono : Monotone α)
    (hDiscFinite : (discontinuitySetOn f a b).Finite)
    (hαCont :
      ∀ ⦃x : ℝ⦄, x ∈ discontinuitySetOn f a b → ContinuousAt α x)
    (heps : 0 < eps) :
    ∃ S : Finset ℝ,
      (∀ x : ℝ, x ∈ S ↔ x ∈ discontinuitySetOn f a b) ∧
      ∃ rho : ℝ → ℝ,
        (∀ c : ℝ, c ∈ S → 0 < rho c) ∧
        (∑ c ∈ S, (α (c + rho c) - α (c - rho c))) < eps ∧
        (↑S : Set ℝ).PairwiseDisjoint
          (fun c : ℝ => Set.Ioo (c - rho c) (c + rho c)) := by
  sorry
end Thm11SourceRoute
end
