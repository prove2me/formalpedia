-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_abs_sheetSum_le_1d273918db5b
-- name    : P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_abs_sheetSum_le_1d273918db5b
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:27:54.097227+00:00
-- url     : https://prove2.me/theorems/b9bd3c5d-2711-4bb0-beae-7c7da80003bf
-- title:
--   P2 M Ground Theory Heights  Heights Chart Int Count Add abs sheet Sum le 1d273918db5b: P2 M Ground Theory Heights  Heights Chart Int Count Add abs sheet Sum le 1d273918db5b
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Int Count Add abs sheet Sum le 1d273918db5b construction uses the P2 M Ground Theory Heights  Heights Chart Int Count Add abs sheet Sum le 1d273918db5b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PChartIntCountAdd.lean#L56-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PChartIntCountAdd.lean#L56-L64

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

theorem P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_abs_sheetSum_le_1d273918db5b {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ} {y : Fin d → ℂ}
    (hfin : (fibre J A y).Finite) (F : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ) :
    |sheetSum J A F y| ≤ sheetSum J A (fun x s => |F x s|) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIntCountAdd».«abs_sheetSum_le» := P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_abs_sheetSum_le_1d273918db5b
