-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_projMap_X_none_3cab59bf1f36
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_projMap_X_none_3cab59bf1f36
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:06:03.009963+00:00
-- url     : https://prove2.me/theorems/16815a93-8f6a-4984-9f55-13914521daab
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof proj Map X none 3cab59bf1f36: P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof proj Map X none 3cab59bf1f
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof proj Map X none 3cab59bf1f36 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof proj Map X none 3cab59bf1f36 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineSectionForms.lean#L47-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineSectionForms.lean#L47-L51

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_projMap_X_none_3cab59bf1f36 (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) (l : Fin M) :
    projMap F y w φ t (X ⟨none, l⟩) =
      C (∑ i, t i * algebraMap Ω Φ (φ l (w i))) * X none := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagLineSectionProof».«projMap_X_none» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_projMap_X_none_3cab59bf1f36
