-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_measurable_sheetSum_0ce06e8414ea
-- name    : P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_measurable_sheetSum_0ce06e8414ea
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:53.209798+00:00
-- url     : https://prove2.me/theorems/7b77debb-54e8-4cb7-aaab-09c5c555c5c3
-- title:
--   P2 M Ground Theory Heights  Heights Sheet Sum Measurable measurable sheet Sum 0ce06e8414ea: P2 M Ground Theory Heights  Heights Sheet Sum Measurable measurable sheet Sum 0ce06e8414ea
-- statement:
--   The P2 M Ground Theory Heights  Heights Sheet Sum Measurable measurable sheet Sum 0ce06e8414ea construction uses the P2 M Ground Theory Heights  Heights Sheet Sum Measurable measurable sheet Sum 0ce06e8414ea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSheetSumMeasurable.lean#L87-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSheetSumMeasurable.lean#L87-L214

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
open Classical

theorem P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_measurable_sheetSum_0ce06e8414ea {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (hA : IsFiniteProjection J A) (Φ : ℝ → ℝ → ℝ) (hΦ : Measurable (Function.uncurry Φ))
    {g : (Fin n → ℂ) → ℝ} (hg : Measurable g) (φ : Fin d → (Fin n → ℂ) → ℝ) :
    Measurable fun y => sheetSum J A
      (fun x s => Φ (g x) (ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y)) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SheetSumMeasurable».«measurable_sheetSum» := P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_measurable_sheetSum_0ce06e8414ea
