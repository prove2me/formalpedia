-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMassCompact_chartAbsDens_le_567434bbc6d4
-- name    : P2M_GroundTheory_Heights__Heights_ChartMassCompact_chartAbsDens_le_567434bbc6d4
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:16:46.136999+00:00
-- url     : https://prove2.me/theorems/5b696696-dd07-5f45-9804-e9b27f7e8e1a
-- title:
--   P2 M Ground Theory Heights  Heights Chart Mass Compact chart Abs Dens le 567434bbc6d4: P2 M Ground Theory Heights  Heights Chart Mass Compact chart Abs Dens le 567434bbc6d4
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Mass Compact chart Abs Dens le 567434bbc6d4 construction uses the P2 M Ground Theory Heights  Heights Chart Mass Compact chart Abs Dens le 567434bbc6d4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PChartMassCompact.lean#L76-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PChartMassCompact.lean#L76-L97

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChartMassCompact
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
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.ChartMassCompact
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartMassCompact_chartAbsDens_le_567434bbc6d4 (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (ψ : Fin d → (Fin n → ℂ) → ℝ) {K B : Set (Fin n → ℂ)} {M : ℝ}
    (hKB : K ⊆ B) (hM : ∀ x ∈ zeroSet J ∩ K, |f x| ≤ M) (hM0 : 0 ≤ M)
    (hvan : ∀ x s, IsSheetAt J A x s → x ∉ K →
      f x * ReciprocityTheory.AnForm.maDens (fun k => ψ k ∘ s) (A *ᵥ x) = 0)
    (y : Fin d → ℂ) (hfin : (fibre J A y).Finite) :
    chartAbsDens J A f ψ y ≤ M * chartAbsDens J A (B.indicator fun _ => 1) ψ y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartMassCompact».«chartAbsDens_le» := P2M_GroundTheory_Heights__Heights_ChartMassCompact_chartAbsDens_le_567434bbc6d4
