-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_hessC_half_log_normSq_add_1b30ac20ecb4
-- name    : P2M_GroundTheory_Heights__Heights_hessC_half_log_normSq_add_1b30ac20ecb4
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:47:37.580515+00:00
-- url     : https://prove2.me/theorems/9d65595a-4e4e-456c-97a8-4056411a994c
-- title:
--   P2 M Ground Theory Heights  Heights hess C half log norm Sq add 1b30ac20ecb4: P2 M Ground Theory Heights  Heights hess C half log norm Sq add 1b30ac20ecb4
-- statement:
--   The P2 M Ground Theory Heights  Heights hess C half log norm Sq add 1b30ac20ecb4 construction uses the P2 M Ground Theory Heights  Heights hess C half log norm Sq add 1b30ac20ecb4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLelongLimitOffZero.lean#L16-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLelongLimitOffZero.lean#L16-L62

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongLimitOffZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHessCCompPluri
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffGradient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongLimitOffZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm
open scoped ContDiff

theorem P2M_GroundTheory_Heights__Heights_hessC_half_log_normSq_add_1b30ac20ecb4 {D : ℕ} (h : (Fin D → ℂ) → ℂ) (y : Fin D → ℂ)
    (hh : AnalyticAt ℂ h y) (hy : h y ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    hessC (fun w => Real.log (‖h w‖ ^ 2 + ε) / 2) y =
      ((ε / (2 * (‖h y‖ ^ 2 + ε) ^ 2) : ℝ) : ℂ) • hessC (fun w => ‖h w‖ ^ 2) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«hessC_half_log_normSq_add» := P2M_GroundTheory_Heights__Heights_hessC_half_log_normSq_add_1b30ac20ecb4
