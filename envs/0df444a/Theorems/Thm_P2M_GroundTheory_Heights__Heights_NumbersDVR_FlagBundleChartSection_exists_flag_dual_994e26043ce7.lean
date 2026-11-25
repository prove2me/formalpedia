-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_exists_flag_dual_994e26043ce7
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_exists_flag_dual_994e26043ce7
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:06:22.937425+00:00
-- url     : https://prove2.me/theorems/44d6b666-f7b0-40a4-b068-0aae654d1132
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section exists flag dual 994e26043ce7: P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section exists flag dual 994e
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section exists flag dual 994e26043ce7 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section exists flag dual 994e26043ce7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleChartSectionTools.lean#L42-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleChartSectionTools.lean#L42-L150

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleChartSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleSectionFormsTools
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PProjIdealFormValue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleChartSectionTools
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_exists_flag_dual_ed946381b07c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundleChartSection
open FlagBundleSectionForms (chartPow chartMono liftNat)
variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]
  {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
variable {N : ℕ} {E : Type} [AddCommGroup E] [Module Ω E]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_exists_flag_dual_994e26043ce7 (y : (Σ k, ι k) → Ω) (B : ChartBundle F (segreVec y) N E)
    (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ) (hfl : IsFlagFrame y B w b)
    (c : ∀ k, ι k) (hc : segreVec y c ≠ 0) (i : Fin N) :
    ∃ ψ : Module.Dual Ω E, (∀ v ∈ B.lat c, ψ v ∈ chartRing F (segreVec y) c) ∧
      (∀ j, j < i → ψ (w j) = 0) ∧ ψ (w i) = (chartPow y c (b i))⁻¹ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagBundleChartSection».«exists_flag_dual» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_exists_flag_dual_994e26043ce7
