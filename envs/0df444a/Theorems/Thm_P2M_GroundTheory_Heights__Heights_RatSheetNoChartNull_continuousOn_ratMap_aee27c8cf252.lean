-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RatSheetNoChartNull_continuousOn_ratMap_aee27c8cf252
-- name    : P2M_GroundTheory_Heights__Heights_RatSheetNoChartNull_continuousOn_ratMap_aee27c8cf252
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:17:36.155807+00:00
-- url     : https://prove2.me/theorems/11f301b1-f7dd-4707-ba7b-a097594dee0a
-- title:
--   P2 M Ground Theory Heights  Heights Rat Sheet No Chart Null continuous On rat Map aee27c8cf252: P2 M Ground Theory Heights  Heights Rat Sheet No Chart Null continuous On rat Map aee27c8cf252
-- statement:
--   The P2 M Ground Theory Heights  Heights Rat Sheet No Chart Null continuous On rat Map aee27c8cf252 construction uses the P2 M Ground Theory Heights  Heights Rat Sheet No Chart Null continuous On rat Map aee27c8cf252 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PRatSheetNoChartNull.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PRatSheetNoChartNull.lean#L18-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatSheetNoChartNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetOnlyNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCriticalImageNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PRatSheetNoChartNull
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.RatSheetNoChartNull
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_RatSheetNoChartNull_continuousOn_ratMap_aee27c8cf252 (p : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ) :
    ContinuousOn (RatChart.ratMap p q) {x | eval x q ≠ 0} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RatSheetNoChartNull».«continuousOn_ratMap» := P2M_GroundTheory_Heights__Heights_RatSheetNoChartNull_continuousOn_ratMap_aee27c8cf252
