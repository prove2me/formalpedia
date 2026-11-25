-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_segreVec_pow_88ac63332cbb
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_segreVec_pow_88ac63332cbb
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:12:47.077167+00:00
-- url     : https://prove2.me/theorems/c9114864-6e5b-5312-8f2a-ebaa1a4e4df8
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof segre Vec pow 88ac63332cbb: P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof segre Vec pow 88ac63332cbb
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof segre Vec pow 88ac63332cbb construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof segre Vec pow 88ac63332cbb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineSectionForms.lean#L173-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineSectionForms.lean#L173-L175

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_segreVec_pow_88ac63332cbb (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (n : ℕ) :
    segreVec y c ^ n = chartZ y c (fun _ => (n : ℤ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagLineSectionProof».«segreVec_pow» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_segreVec_pow_88ac63332cbb
