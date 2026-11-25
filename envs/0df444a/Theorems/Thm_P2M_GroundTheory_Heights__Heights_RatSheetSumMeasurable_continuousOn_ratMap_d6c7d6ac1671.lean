-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RatSheetSumMeasurable_continuousOn_ratMap_d6c7d6ac1671
-- name    : P2M_GroundTheory_Heights__Heights_RatSheetSumMeasurable_continuousOn_ratMap_d6c7d6ac1671
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:16:51.671204+00:00
-- url     : https://prove2.me/theorems/dd79651a-924e-4ee1-9c57-46f1e1bf8a39
-- title:
--   P2 M Ground Theory Heights  Heights Rat Sheet Sum Measurable continuous On rat Map d6c7d6ac1671: P2 M Ground Theory Heights  Heights Rat Sheet Sum Measurable continuous On rat Map d6c7d6ac1671
-- statement:
--   The P2 M Ground Theory Heights  Heights Rat Sheet Sum Measurable continuous On rat Map d6c7d6ac1671 construction uses the P2 M Ground Theory Heights  Heights Rat Sheet Sum Measurable continuous On rat Map d6c7d6ac1671 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PRatSheetSumMeasurable.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PRatSheetSumMeasurable.lean#L16-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PRatSheetSumMeasurable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ComplexSets
open GroundTheory.Heights₂.Heights.RatSheetSumMeasurable
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_RatSheetSumMeasurable_continuousOn_ratMap_d6c7d6ac1671 (p : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ) :
    ContinuousOn (RatChart.ratMap p q) {z | eval z q ≠ 0} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RatSheetSumMeasurable».«continuousOn_ratMap» := P2M_GroundTheory_Heights__Heights_RatSheetSumMeasurable_continuousOn_ratMap_d6c7d6ac1671
