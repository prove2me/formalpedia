-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_chartPow_natCast_95b9d4002130
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_chartPow_natCast_95b9d4002130
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:18.199801+00:00
-- url     : https://prove2.me/theorems/64f88f50-ae2a-4ea4-90a8-0d71d6ee635d
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section chart Pow nat Cast 95b9d4002130: P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section chart Pow nat Cast
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section chart Pow nat Cast 95b9d4002130 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section chart Pow nat Cast 95b9d4002130 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleChartSectionTools.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleChartSectionTools.lean#L30-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleChartSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleSectionFormsTools
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PProjIdealFormValue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleChartSectionTools
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_chartPow_natCast_864f6fcab797

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_chartPow_natCast_95b9d4002130 (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (α : K → ℕ) :
    chartPow y c (fun k => (α k : ℤ)) = ∏ k, y ⟨k, c k⟩ ^ α k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagBundleChartSection».«chartPow_natCast» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_chartPow_natCast_95b9d4002130
