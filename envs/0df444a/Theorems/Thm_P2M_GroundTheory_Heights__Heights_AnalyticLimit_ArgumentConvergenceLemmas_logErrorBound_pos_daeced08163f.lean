-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_ArgumentConvergenceLemmas_logErrorBound_pos_daeced08163f
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_ArgumentConvergenceLemmas_logErrorBound_pos_daeced08163f
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:38:06.776928+00:00
-- url     : https://prove2.me/theorems/80a1a81f-cbbd-4657-9786-dfd21e990901
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit Argument Convergence Lemmas log Error Bound pos daeced08163f: P2 M Ground Theory Heights  Heights Analytic Limit Argument Convergence Lemmas log Erro
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit Argument Convergence Lemmas log Error Bound pos daeced08163f construction uses the P2 M Ground Theory Heights  Heights Analytic Limit Argument Convergence Lemmas log Error Bound pos daeced08163f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/NormIteratedFDerivCompLeOfIsOpen.lean#L118-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/NormIteratedFDerivCompLeOfIsOpen.lean#L118-L129

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

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_ArgumentConvergenceLemmas_logErrorBound_pos_daeced08163f {C t : ℝ} (hC : 0 < C) (ht : 0 < t) (ht1 : t < Real.exp (-1)) :
    0 < errorWithLinear C t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«ArgumentConvergenceLemmas».«logErrorBound_pos» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_ArgumentConvergenceLemmas_logErrorBound_pos_daeced08163f
