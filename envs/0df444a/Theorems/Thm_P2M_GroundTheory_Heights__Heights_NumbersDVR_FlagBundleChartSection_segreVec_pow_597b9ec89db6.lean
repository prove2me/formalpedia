-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_segreVec_pow_597b9ec89db6
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_segreVec_pow_597b9ec89db6
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:53.948972+00:00
-- url     : https://prove2.me/theorems/3db124f1-df21-444b-8e09-b63df67dea55
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section segre Vec pow 597b9ec89db6: P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section segre Vec pow 597b9ec89d
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section segre Vec pow 597b9ec89db6 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section segre Vec pow 597b9ec89db6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleChartSectionTools.lean#L34-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleChartSectionTools.lean#L34-L36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleChartSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleSectionFormsTools
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PProjIdealFormValue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleChartSectionTools
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_segreVec_pow_851cfbba86d7

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_segreVec_pow_597b9ec89db6 (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (n : ℕ) :
    segreVec y c ^ n = chartPow y c (fun _ => (n : ℤ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagBundleChartSection».«segreVec_pow» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_segreVec_pow_597b9ec89db6
