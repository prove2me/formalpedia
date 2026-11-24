-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_measurable_maDens_fedcbcd77e6d
-- name    : P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_measurable_maDens_fedcbcd77e6d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:13:51.688795+00:00
-- url     : https://prove2.me/theorems/096fc935-d729-40e0-8b85-45a1ba3c55d3
-- title:
--   P2 M Ground Theory Heights  Heights Sheet Sum Measurable measurable ma Dens fedcbcd77e6d: P2 M Ground Theory Heights  Heights Sheet Sum Measurable measurable ma Dens fedcbcd77e6d
-- statement:
--   The P2 M Ground Theory Heights  Heights Sheet Sum Measurable measurable ma Dens fedcbcd77e6d construction uses the P2 M Ground Theory Heights  Heights Sheet Sum Measurable measurable ma Dens fedcbcd77e6d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSheetSumMeasurable.lean#L17-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSheetSumMeasurable.lean#L17-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsSheetMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GraphChartEventuallyEqSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LogIntegrableOnOfLogIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
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
open GroundTheory.Heights₂.Heights.SheetSumMeasurable
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_measurable_maDens_fedcbcd77e6d {D : ℕ} (ψ : Fin D → (Fin D → ℂ) → ℝ) :
    Measurable (ReciprocityTheory.AnForm.maDens ψ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SheetSumMeasurable».«measurable_maDens» := P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_measurable_maDens_fedcbcd77e6d
