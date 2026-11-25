-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_segreVec_ne_zero_of_live_7f57050cfd7f
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_segreVec_ne_zero_of_live_7f57050cfd7f
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:07:30.207166+00:00
-- url     : https://prove2.me/theorems/ed0cd3a1-9b95-45d2-9add-f8d9516c506c
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof segre Vec ne zero of live 7f57050cfd7f: P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof segre Vec ne zer
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof segre Vec ne zero of live 7f57050cfd7f construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof segre Vec ne zero of live 7f57050cfd7f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineSectionForms.lean#L185-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineSectionForms.lean#L185-L187

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_segreVec_ne_zero_of_live_7f57050cfd7f {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    segreVec y c ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagLineSectionProof».«segreVec_ne_zero_of_live» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_segreVec_ne_zero_of_live_7f57050cfd7f
