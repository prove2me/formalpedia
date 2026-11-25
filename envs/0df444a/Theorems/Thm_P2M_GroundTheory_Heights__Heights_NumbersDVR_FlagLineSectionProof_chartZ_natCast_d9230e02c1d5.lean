-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_chartZ_natCast_d9230e02c1d5
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_chartZ_natCast_d9230e02c1d5
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:33:11.601394+00:00
-- url     : https://prove2.me/theorems/8e9b70ed-886a-49d3-8889-656e0f4c99af
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof chart Z nat Cast d9230e02c1d5: P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof chart Z nat Cast d9230e02
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof chart Z nat Cast d9230e02c1d5 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof chart Z nat Cast d9230e02c1d5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineSectionForms.lean#L169-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineSectionForms.lean#L169-L171

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagLineSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagLineSectionForms
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
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagLineSectionProof
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type} {Ω : Type*} [Field Ω]
  {F : Type*} [Field F] [Algebra F Ω] {N M : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]
  {Φ : Type*} [Field Φ] [Algebra Ω Φ]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_chartZ_natCast_d9230e02c1d5 (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (α : K → ℕ) :
    chartZ y c (fun k => (α k : ℤ)) = ∏ k, y ⟨k, c k⟩ ^ α k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagLineSectionProof».«chartZ_natCast» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_chartZ_natCast_d9230e02c1d5
