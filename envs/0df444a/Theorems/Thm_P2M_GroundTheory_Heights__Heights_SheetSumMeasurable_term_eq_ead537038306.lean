-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_term_eq_ead537038306
-- name    : P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_term_eq_ead537038306
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:10.581224+00:00
-- url     : https://prove2.me/theorems/e8835cf2-9618-4501-a383-1263f150775b
-- title:
--   P2 M Ground Theory Heights  Heights Sheet Sum Measurable term eq ead537038306: P2 M Ground Theory Heights  Heights Sheet Sum Measurable term eq ead537038306
-- statement:
--   The P2 M Ground Theory Heights  Heights Sheet Sum Measurable term eq ead537038306 construction uses the P2 M Ground Theory Heights  Heights Sheet Sum Measurable term eq ead537038306 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSheetSumMeasurable.lean#L51-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSheetSumMeasurable.lean#L51-L57

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

theorem P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_term_eq_ead537038306 {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (Φ : ℝ → ℝ → ℝ) (g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) {x : Fin n → ℂ}
    {s : (Fin d → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s) (h : ∃ s, IsSheetAt J A x s) :
    Φ (g x) (ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) (A *ᵥ x)) =
      Φ (g x) (ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) (A *ᵥ x)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SheetSumMeasurable».«term_eq» := P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_term_eq_ead537038306
