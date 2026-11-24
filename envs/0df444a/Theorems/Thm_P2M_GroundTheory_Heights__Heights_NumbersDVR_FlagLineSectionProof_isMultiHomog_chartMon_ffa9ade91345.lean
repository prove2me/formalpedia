-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_isMultiHomog_chartMon_ffa9ade91345
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_isMultiHomog_chartMon_ffa9ade91345
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:18.822523+00:00
-- url     : https://prove2.me/theorems/c44dcaa2-9b57-44b3-afd7-f5f7536825f8
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof is Multi Homog chart Mon ffa9ade91345: P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof is Multi Homog ch
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof is Multi Homog chart Mon ffa9ade91345 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof is Multi Homog chart Mon ffa9ade91345 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineSectionForms.lean#L74-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineSectionForms.lean#L74-L85

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_isMultiHomog_chartMon_ffa9ade91345 (c : ∀ k, ι k) (α : K → ℕ) :
    IsMultiHomog (chartMon F M c α) (liftN α) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagLineSectionProof».«isMultiHomog_chartMon» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_isMultiHomog_chartMon_ffa9ade91345
