-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_isMultiHomog_X_none_21441bf27d48
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_isMultiHomog_X_none_21441bf27d48
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:31:48.465531+00:00
-- url     : https://prove2.me/theorems/2ba0d002-1175-48a0-8c61-759ea57b2ba4
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof is Multi Homog X none 21441bf27d48: P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof is Multi Homog X non
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof is Multi Homog X none 21441bf27d48 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof is Multi Homog X none 21441bf27d48 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineSectionForms.lean#L87-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineSectionForms.lean#L87-L90

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_isMultiHomog_X_none_21441bf27d48 (l : Fin M) :
    IsMultiHomog (X ⟨none, l⟩ : MRing (bundleIdx ι M) F) (Pi.single none 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagLineSectionProof».«isMultiHomog_X_none» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_isMultiHomog_X_none_21441bf27d48
