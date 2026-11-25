-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BranchChartInt_chartDens_indicator_image_d6d60c4b9759
-- name    : P2M_GroundTheory_Heights__Heights_BranchChartInt_chartDens_indicator_image_d6d60c4b9759
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:16:33.38828+00:00
-- url     : https://prove2.me/theorems/5b8b067d-fcb5-49f5-8320-2c4acfa34e8c
-- title:
--   P2 M Ground Theory Heights  Heights Branch Chart Int chart Dens indicator image d6d60c4b9759: P2 M Ground Theory Heights  Heights Branch Chart Int chart Dens indicator image d6d60c4b9759
-- statement:
--   The P2 M Ground Theory Heights  Heights Branch Chart Int chart Dens indicator image d6d60c4b9759 construction uses the P2 M Ground Theory Heights  Heights Branch Chart Int chart Dens indicator image d6d60c4b9759 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PBranchChartInt.lean#L34-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PBranchChartInt.lean#L34-L62

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchChartInt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicFibreSumInt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchSheetAE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PBranchChartInt
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm.A
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.BranchChartInt
open Classical

theorem P2M_GroundTheory_Heights__Heights_BranchChartInt_chartDens_indicator_image_d6d60c4b9759 {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    {p : Fin n → ℂ} (γ : VarBranch J d p) (g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ)
    (y : Fin d → ℂ) :
    chartDens J A (γ.image.indicator g) φ y =
      ∑ᶠ t ∈ {t | t ∈ Metric.ball (0 : Fin d → ℂ) γ.radius ∧ A *ᵥ γ.toFun t = y},
        (if h : ∃ s, IsSheetAt J A (γ.toFun t) s then
          g (γ.toFun t) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) (A *ᵥ γ.toFun t) else 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BranchChartInt».«chartDens_indicator_image» := P2M_GroundTheory_Heights__Heights_BranchChartInt_chartDens_indicator_image_d6d60c4b9759
