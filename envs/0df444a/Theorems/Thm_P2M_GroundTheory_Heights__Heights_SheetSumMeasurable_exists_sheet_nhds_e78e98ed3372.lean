-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_exists_sheet_nhds_e78e98ed3372
-- name    : P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_exists_sheet_nhds_e78e98ed3372
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:11:36.877671+00:00
-- url     : https://prove2.me/theorems/2589c913-8fd2-4dc5-9e25-ea5aa40fb043
-- title:
--   P2 M Ground Theory Heights  Heights Sheet Sum Measurable exists sheet nhds e78e98ed3372: P2 M Ground Theory Heights  Heights Sheet Sum Measurable exists sheet nhds e78e98ed3372
-- statement:
--   The P2 M Ground Theory Heights  Heights Sheet Sum Measurable exists sheet nhds e78e98ed3372 construction uses the P2 M Ground Theory Heights  Heights Sheet Sum Measurable exists sheet nhds e78e98ed3372 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSheetSumMeasurable.lean#L59-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSheetSumMeasurable.lean#L59-L76

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

theorem P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_exists_sheet_nhds_e78e98ed3372 {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (x : Fin n → ℂ) :
    ∃ (s : (Fin d → ℂ) → Fin n → ℂ) (U : Set (Fin d → ℂ)) (W : Set (Fin n → ℂ)),
      IsOpen U ∧ IsOpen W ∧ ContinuousOn s U ∧ (∀ y ∈ U, A *ᵥ s y = y ∧ s y ∈ zeroSet J) ∧
      (∀ x' ∈ zeroSet J ∩ W, A *ᵥ x' ∈ U ∧ IsSheetAt J A x' s) ∧
      ((∃ s, IsSheetAt J A x s) → x ∈ W) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SheetSumMeasurable».«exists_sheet_nhds» := P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_exists_sheet_nhds_e78e98ed3372
