-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_abs_indicator_mul_le_da6dab3ba3ec
-- name    : P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_abs_indicator_mul_le_da6dab3ba3ec
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:28:41.664116+00:00
-- url     : https://prove2.me/theorems/a0b09c78-b629-4107-a0b9-262f3ade66c8
-- title:
--   P2 M Ground Theory Heights  Heights Chart Int Count Add abs indicator mul le da6dab3ba3ec: P2 M Ground Theory Heights  Heights Chart Int Count Add abs indicator mul le da6dab3ba3ec
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Int Count Add abs indicator mul le da6dab3ba3ec construction uses the P2 M Ground Theory Heights  Heights Chart Int Count Add abs indicator mul le da6dab3ba3ec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PChartIntCountAdd.lean#L84-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PChartIntCountAdd.lean#L84-L86

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartIntCountAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChartIntCountAdd
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
open GroundTheory.Heights₂.Heights.ChartIntCountAdd
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_abs_indicator_mul_le_da6dab3ba3ec (S : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → ℝ) (x : Fin n → ℂ) (c : ℝ) :
    |S.indicator f x * c| ≤ |f x * c| := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIntCountAdd».«abs_indicator_mul_le» := P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_abs_indicator_mul_le_da6dab3ba3ec
