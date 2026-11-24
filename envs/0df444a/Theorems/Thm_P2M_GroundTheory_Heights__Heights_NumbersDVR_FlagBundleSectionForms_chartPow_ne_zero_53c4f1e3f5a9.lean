-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_chartPow_ne_zero_53c4f1e3f5a9
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_chartPow_ne_zero_53c4f1e3f5a9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:55:17.609724+00:00
-- url     : https://prove2.me/theorems/aead4e19-789c-4bbd-a2d4-b15d299ed241
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Section Forms chart Pow ne zero 53c4f1e3f5a9: P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Section Forms chart Pow ne zero 53
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Section Forms chart Pow ne zero 53c4f1e3f5a9 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Section Forms chart Pow ne zero 53c4f1e3f5a9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleSectionFormsTools.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleSectionFormsTools.lean#L25-L27

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_chartPow_ne_zero_53c4f1e3f5a9 {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hY : ∀ k, y ⟨k, c k⟩ ≠ 0) (d : K → ℤ) :
    chartPow y c d ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagBundleSectionForms».«chartPow_ne_zero» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_chartPow_ne_zero_53c4f1e3f5a9
