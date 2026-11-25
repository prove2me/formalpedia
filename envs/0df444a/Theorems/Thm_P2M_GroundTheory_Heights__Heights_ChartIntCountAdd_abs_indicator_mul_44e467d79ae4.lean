-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_abs_indicator_mul_44e467d79ae4
-- name    : P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_abs_indicator_mul_44e467d79ae4
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:27:37.757352+00:00
-- url     : https://prove2.me/theorems/80a51503-7e15-4edb-a71d-4bb4f499c24e
-- title:
--   P2 M Ground Theory Heights  Heights Chart Int Count Add abs indicator mul 44e467d79ae4: P2 M Ground Theory Heights  Heights Chart Int Count Add abs indicator mul 44e467d79ae4
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Int Count Add abs indicator mul 44e467d79ae4 construction uses the P2 M Ground Theory Heights  Heights Chart Int Count Add abs indicator mul 44e467d79ae4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PChartIntCountAdd.lean#L80-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PChartIntCountAdd.lean#L80-L82

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

theorem P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_abs_indicator_mul_44e467d79ae4 (S : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → ℝ) (x : Fin n → ℂ) (c : ℝ) :
    |S.indicator f x * c| = S.indicator (fun z => |f z * c|) x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIntCountAdd».«abs_indicator_mul» := P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_abs_indicator_mul_44e467d79ae4
