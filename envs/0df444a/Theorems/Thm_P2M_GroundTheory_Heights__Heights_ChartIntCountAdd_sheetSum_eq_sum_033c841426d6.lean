-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_sheetSum_eq_sum_033c841426d6
-- name    : P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_sheetSum_eq_sum_033c841426d6
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:14.708857+00:00
-- url     : https://prove2.me/theorems/ed41cb92-1003-4c7b-80d3-c8c0fd0cbe45
-- title:
--   P2 M Ground Theory Heights  Heights Chart Int Count Add sheet Sum eq sum 033c841426d6: P2 M Ground Theory Heights  Heights Chart Int Count Add sheet Sum eq sum 033c841426d6
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Int Count Add sheet Sum eq sum 033c841426d6 construction uses the P2 M Ground Theory Heights  Heights Chart Int Count Add sheet Sum eq sum 033c841426d6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PChartIntCountAdd.lean#L38-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PChartIntCountAdd.lean#L38-L43

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
open Classical

theorem P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_sheetSum_eq_sum_033c841426d6 {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ} {y : Fin d → ℂ}
    (hfin : (fibre J A y).Finite) (F : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ) :
    sheetSum J A F y =
      ∑ x ∈ hfin.toFinset, (if h : ∃ s, IsSheetAt J A x s then F x h.choose else 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIntCountAdd».«sheetSum_eq_sum» := P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_sheetSum_eq_sum_033c841426d6
