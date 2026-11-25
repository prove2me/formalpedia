-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_ArgumentConvergenceLemmas_norm_fderiv_fderiv_eq_938ca658f52c
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_ArgumentConvergenceLemmas_norm_fderiv_fderiv_eq_938ca658f52c
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:41:44.403055+00:00
-- url     : https://prove2.me/theorems/c7cb3c59-0c5e-54de-bdc0-49e8d0517a8a
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit Argument Convergence Lemmas norm fderiv fderiv eq 938ca658f52c: P2 M Ground Theory Heights  Heights Analytic Limit Argument Convergence Lemmas norm f
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit Argument Convergence Lemmas norm fderiv fderiv eq 938ca658f52c construction uses the P2 M Ground Theory Heights  Heights Analytic Limit Argument Convergence Lemmas norm fderiv fderiv eq 938ca658f52c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/NormIteratedFDerivCompLeOfIsOpen.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/NormIteratedFDerivCompLeOfIsOpen.lean#L41-L43

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

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_ArgumentConvergenceLemmas_norm_fderiv_fderiv_eq_938ca658f52c (g : E → F) (y : E) :
    ‖fderiv ℝ (fderiv ℝ g) y‖ = ‖iteratedFDeriv ℝ 2 g y‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«ArgumentConvergenceLemmas».«norm_fderiv_fderiv_eq» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_ArgumentConvergenceLemmas_norm_fderiv_fderiv_eq_938ca658f52c
