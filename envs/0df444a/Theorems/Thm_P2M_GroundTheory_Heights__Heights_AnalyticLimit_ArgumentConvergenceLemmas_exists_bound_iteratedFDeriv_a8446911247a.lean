-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_ArgumentConvergenceLemmas_exists_bound_iteratedFDeriv_a8446911247a
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_ArgumentConvergenceLemmas_exists_bound_iteratedFDeriv_a8446911247a
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:37:42.967301+00:00
-- url     : https://prove2.me/theorems/3f59d3d1-c36b-46a2-91f5-4ddcd438baf1
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit Argument Convergence Lemmas exists bound iterated FDeriv a8446911247a: P2 M Ground Theory Heights  Heights Analytic Limit Argument Convergence Lemmas
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit Argument Convergence Lemmas exists bound iterated FDeriv a8446911247a construction uses the P2 M Ground Theory Heights  Heights Analytic Limit Argument Convergence Lemmas exists bound iterated FDeriv a8446911247a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/NormIteratedFDerivCompLeOfIsOpen.lean#L74-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/NormIteratedFDerivCompLeOfIsOpen.lean#L74-L87

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_RegularizedMaxC2ExampleRealLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsOpenKappaOpenNeighbourhood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_NormIteratedFDerivCompLeOfIsOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open GroundTheory.Heights₂.Heights.AnalyticLimit.ArgumentConvergenceLemmas
open Filter Topology Metric Set MeasureTheory
open scoped ContDiff
open ReciprocityTheory.AnForm.A (Mollifier molli shrink)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (errE errorWithLinear ell)
noncomputable section
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_ArgumentConvergenceLemmas_exists_bound_iteratedFDeriv_a8446911247a {f : E → F} {s K : Set E} (hs : IsOpen s)
    (hf : ContDiffOn ℝ 2 f s) (hK : IsCompact K) (hKs : K ⊆ s) :
    ∃ B : ℝ, ∀ i : ℕ, i ≤ 2 → ∀ y ∈ K, ‖iteratedFDeriv ℝ i f y‖ ≤ B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«ArgumentConvergenceLemmas».«exists_bound_iteratedFDeriv» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_ArgumentConvergenceLemmas_exists_bound_iteratedFDeriv_a8446911247a
