-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_ArgumentConvergenceLemmas_norm_iteratedFDeriv_sub_eq_db13c53b8c02
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_ArgumentConvergenceLemmas_norm_iteratedFDeriv_sub_eq_db13c53b8c02
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:35:20.949819+00:00
-- url     : https://prove2.me/theorems/6f96d5c8-cbab-5ebb-85c9-e399f9b66041
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit Argument Convergence Lemmas norm iterated FDeriv sub eq db13c53b8c02: P2 M Ground Theory Heights  Heights Analytic Limit Argument Convergence Lemmas
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit Argument Convergence Lemmas norm iterated FDeriv sub eq db13c53b8c02 construction uses the P2 M Ground Theory Heights  Heights Analytic Limit Argument Convergence Lemmas norm iterated FDeriv sub eq db13c53b8c02 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/NormIteratedFDerivCompLeOfIsOpen.lean#L45-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/NormIteratedFDerivCompLeOfIsOpen.lean#L45-L57

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

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_ArgumentConvergenceLemmas_norm_iteratedFDeriv_sub_eq_db13c53b8c02 {a b : E → ℝ} {V : Set E} (hV : IsOpen V)
    (ha : ContDiffOn ℝ 2 a V) (hb : ContDiffOn ℝ 2 b V) {z : E} (hz : z ∈ V) :
    ‖iteratedFDeriv ℝ 0 (fun y => a y - b y) z‖ = ‖a z - b z‖ ∧
      ‖iteratedFDeriv ℝ 1 (fun y => a y - b y) z‖ = ‖fderiv ℝ a z - fderiv ℝ b z‖ ∧
      ‖iteratedFDeriv ℝ 2 (fun y => a y - b y) z‖ =
        ‖fderiv ℝ (fderiv ℝ a) z - fderiv ℝ (fderiv ℝ b) z‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«ArgumentConvergenceLemmas».«norm_iteratedFDeriv_sub_eq» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_ArgumentConvergenceLemmas_norm_iteratedFDeriv_sub_eq_db13c53b8c02
