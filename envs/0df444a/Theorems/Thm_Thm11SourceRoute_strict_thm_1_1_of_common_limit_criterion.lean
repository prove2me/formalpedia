-- Prove2me | Theorems.Thm_Thm11SourceRoute_strict_thm_1_1_of_common_limit_criterion
-- name    : Thm11SourceRoute.strict_thm_1_1_of_common_limit_criterion
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:10:43.749191+00:00
-- url     : https://prove2.me/theorems/627d0d62-4950-4604-a40e-23996b1d302b
-- title:
--   ProbabilityTheory_chapter_01_thm_1_1_common_limit_F001: Thm11SourceRoute.strict_thm_1_1_of_common_limit_criterion
-- statement:
--   Source theorem `Thm11SourceRoute.strict_thm_1_1_of_common_limit_criterion` extracted from `ProbabilityTheory.chapter_01.thm_1_1_common_limit`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_common_limit.lean

import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_common_limit_F001
import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_basic_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_basic_F001
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_common_limit_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_darboux_gap_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_finite_discontinuity_F000
import Mathlib.Data.List.GetD
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep
open Finset BigOperators
open Set Topology
noncomputable section
namespace Thm11SourceRoute

theorem strict_thm_1_1_of_common_limit_criterion
    (hcriterion : StrictFiniteDiscontinuityCommonLimitCriterion)
    {f α : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hα_mono : Monotone α)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (hDiscFinite : (discontinuitySetOn f a b).Finite)
    (hαCont : ∀ ⦃x : ℝ⦄, x ∈ discontinuitySetOn f a b → ContinuousAt α x) :
    RSIntegrable f α a b := by
  sorry
end Thm11SourceRoute
end
