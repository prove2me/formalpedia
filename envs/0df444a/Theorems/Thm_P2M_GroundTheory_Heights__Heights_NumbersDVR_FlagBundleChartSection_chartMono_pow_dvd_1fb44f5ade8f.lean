-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_chartMono_pow_dvd_1fb44f5ade8f
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_chartMono_pow_dvd_1fb44f5ade8f
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:05:33.469807+00:00
-- url     : https://prove2.me/theorems/7cfe891b-96d8-4c84-816f-6d3acfe07b2e
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section chart Mono pow dvd 1fb44f5ade8f: P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section chart Mono pow dvd
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section chart Mono pow dvd 1fb44f5ade8f construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section chart Mono pow dvd 1fb44f5ade8f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleChartSectionTools.lean#L182-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleChartSectionTools.lean#L182-L191

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleChartSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleSectionFormsTools
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PProjIdealFormValue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleChartSectionTools
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
variable {M N : ℕ} {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_chartMono_pow_dvd_1fb44f5ade8f (c : ∀ k, ι k) (δ : K → ℕ) (D : ℕ) :
    chartMono (F := F) M c δ ^ D ∣
      (∏ k, (X ⟨some k, c k⟩ : MRing (bundleIdx ι M) F)) ^ (D * ∑ k, δ k) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagBundleChartSection».«chartMono_pow_dvd» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_chartMono_pow_dvd_1fb44f5ade8f
