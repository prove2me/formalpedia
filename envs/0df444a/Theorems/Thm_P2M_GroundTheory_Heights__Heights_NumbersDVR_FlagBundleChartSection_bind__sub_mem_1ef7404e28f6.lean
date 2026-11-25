-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_bind__sub_mem_1ef7404e28f6
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_bind__sub_mem_1ef7404e28f6
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:05:34.980255+00:00
-- url     : https://prove2.me/theorems/b9eda276-383d-4051-b8e8-ec439169c3a8
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section bind  sub mem 1ef7404e28f6: P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section bind  sub mem 1ef7404e28
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section bind  sub mem 1ef7404e28f6 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section bind  sub mem 1ef7404e28f6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleChartSectionTools.lean#L378-L389
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleChartSectionTools.lean#L378-L389

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_bind__sub_mem_1ef7404e28f6 {σ R : Type*} [CommRing R] (I : Ideal (MvPolynomial σ R)) (g g' : σ → MvPolynomial σ R)
    (h : ∀ v, g' v - g v ∈ I) (q : MvPolynomial σ R) : bind₁ g' q - bind₁ g q ∈ I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagBundleChartSection».«bind₁_sub_mem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_bind__sub_mem_1ef7404e28f6
