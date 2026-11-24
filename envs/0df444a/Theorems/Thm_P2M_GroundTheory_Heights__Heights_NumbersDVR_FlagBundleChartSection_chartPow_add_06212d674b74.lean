-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_chartPow_add_06212d674b74
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_chartPow_add_06212d674b74
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:16.652247+00:00
-- url     : https://prove2.me/theorems/bee4b2f6-6ea0-4b73-8ee9-6130e56a8d57
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section chart Pow add 06212d674b74: P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section chart Pow add 06212d674b
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section chart Pow add 06212d674b74 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section chart Pow add 06212d674b74 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleChartSectionTools.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleChartSectionTools.lean#L22-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleChartSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleSectionFormsTools
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PProjIdealFormValue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleChartSectionTools
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_chartPow_add_24c459fd04ad

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_chartPow_add_06212d674b74 {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hY : ∀ k, y ⟨k, c k⟩ ≠ 0) (d d' : K → ℤ) :
    chartPow y c (d + d') = chartPow y c d * chartPow y c d' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagBundleChartSection».«chartPow_add» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_chartPow_add_06212d674b74
