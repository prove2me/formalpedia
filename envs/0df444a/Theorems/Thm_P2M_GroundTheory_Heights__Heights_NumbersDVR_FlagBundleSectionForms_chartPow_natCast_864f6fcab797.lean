-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_chartPow_natCast_864f6fcab797
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_chartPow_natCast_864f6fcab797
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:55:23.162604+00:00
-- url     : https://prove2.me/theorems/dc7c8ce6-e367-4f3f-9467-6e8c3cd7378c
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Section Forms chart Pow nat Cast 864f6fcab797: P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Section Forms chart Pow nat Cast
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Section Forms chart Pow nat Cast 864f6fcab797 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Section Forms chart Pow nat Cast 864f6fcab797 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleSectionFormsTools.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleSectionFormsTools.lean#L29-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleSectionFormsTools
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
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundleSectionForms
variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]
  {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_chartPow_natCast_864f6fcab797 (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (α : K → ℕ) :
    chartPow y c (fun k => (α k : ℤ)) = ∏ k, y ⟨k, c k⟩ ^ α k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagBundleSectionForms».«chartPow_natCast» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_chartPow_natCast_864f6fcab797
