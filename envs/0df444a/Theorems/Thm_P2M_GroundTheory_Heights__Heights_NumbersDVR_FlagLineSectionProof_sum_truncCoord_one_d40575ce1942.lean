-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_sum_truncCoord_one_d40575ce1942
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_sum_truncCoord_one_d40575ce1942
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:09:29.496861+00:00
-- url     : https://prove2.me/theorems/011fea39-b3f6-41f9-89b3-1ced5296e948
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof sum trunc Coord one d40575ce1942: P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof sum trunc Coord one d4
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof sum trunc Coord one d40575ce1942 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof sum trunc Coord one d40575ce1942 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineSectionForms.lean#L53-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineSectionForms.lean#L53-L61

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_sum_truncCoord_one_d40575ce1942 (t : Fin N → Φ) (h0 : 0 < N) (z : Fin N → Φ) :
    ∑ i, truncCoord t 1 i * z i = t ⟨0, h0⟩ * z ⟨0, h0⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagLineSectionProof».«sum_truncCoord_one» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_sum_truncCoord_one_d40575ce1942
