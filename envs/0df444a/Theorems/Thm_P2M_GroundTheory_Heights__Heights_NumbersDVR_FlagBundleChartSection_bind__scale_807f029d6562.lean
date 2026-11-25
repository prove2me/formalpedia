-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_bind__scale_807f029d6562
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_bind__scale_807f029d6562
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:06:02.083931+00:00
-- url     : https://prove2.me/theorems/64b3348f-8694-43a0-90e0-1a5fca5bbf53
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section bind  scale 807f029d6562: P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section bind  scale 807f029d6562
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section bind  scale 807f029d6562 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section bind  scale 807f029d6562 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleChartSectionTools.lean#L361-L376
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleChartSectionTools.lean#L361-L376

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_bind__scale_807f029d6562 (u : MRing (bundleIdx ι M) F) {q : MRing (bundleIdx ι M) F} {d : Option K → ℕ}
    (hq : IsMultiHomog q d) :
    bind₁ (fun v => u ^ blockWeight (bundleIdx ι M) v none * X v) q = u ^ d none * q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagBundleChartSection».«bind₁_scale» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_bind__scale_807f029d6562
