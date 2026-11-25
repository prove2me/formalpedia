-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_isMultiHomog_sub_f3f3a0c7d185
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_isMultiHomog_sub_f3f3a0c7d185
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:06:50.554706+00:00
-- url     : https://prove2.me/theorems/b1e6c694-9786-4de6-9118-920cb273d21d
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section is Multi Homog sub f3f3a0c7d185: P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section is Multi Homog sub
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section is Multi Homog sub f3f3a0c7d185 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section is Multi Homog sub f3f3a0c7d185 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleChartSectionTools.lean#L391-L394
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleChartSectionTools.lean#L391-L394

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_isMultiHomog_sub_f3f3a0c7d185 {f g : MRing (bundleIdx ι M) F} {d : Option K → ℕ} (hf : IsMultiHomog f d)
    (hg : IsMultiHomog g d) : IsMultiHomog (f - g) d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagBundleChartSection».«isMultiHomog_sub» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_isMultiHomog_sub_f3f3a0c7d185
