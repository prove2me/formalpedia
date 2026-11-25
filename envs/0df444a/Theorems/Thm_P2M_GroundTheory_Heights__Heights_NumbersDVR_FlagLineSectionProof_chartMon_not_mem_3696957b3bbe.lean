-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_chartMon_not_mem_3696957b3bbe
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_chartMon_not_mem_3696957b3bbe
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:31:10.184518+00:00
-- url     : https://prove2.me/theorems/77f13c79-6cc3-47a9-8f97-63bfb4a24f78
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof chart Mon not mem 3696957b3bbe: P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof chart Mon not mem 369695
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof chart Mon not mem 3696957b3bbe construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof chart Mon not mem 3696957b3bbe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineSection.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineSection.lean#L18-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagLineSectionSplit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagLineSection
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
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type*} [Field F] {M : ℕ}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_chartMon_not_mem_3696957b3bbe {W : Ideal (MRing (bundleIdx ι M) F)} [hW : W.IsPrime] {c : ∀ k, ι k}
    (hc : ∀ k, (X ⟨some k, c k⟩ : MRing (bundleIdx ι M) F) ∉ W) (α : K → ℕ) :
    chartMon F M c α ∉ W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagLineSectionProof».«chartMon_not_mem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_chartMon_not_mem_3696957b3bbe
