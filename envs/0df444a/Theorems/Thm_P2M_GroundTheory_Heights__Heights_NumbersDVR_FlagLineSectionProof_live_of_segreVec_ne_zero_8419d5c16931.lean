-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_live_of_segreVec_ne_zero_8419d5c16931
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_live_of_segreVec_ne_zero_8419d5c16931
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:04.567156+00:00
-- url     : https://prove2.me/theorems/5bc74b37-40f9-4590-b221-d1b433d94859
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof live of segre Vec ne zero 8419d5c16931: P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof live of segre Ve
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof live of segre Vec ne zero 8419d5c16931 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof live of segre Vec ne zero 8419d5c16931 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineSectionForms.lean#L181-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineSectionForms.lean#L181-L183

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_live_of_segreVec_ne_zero_8419d5c16931 {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : segreVec y c ≠ 0) :
    ∀ k, y ⟨k, c k⟩ ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagLineSectionProof».«live_of_segreVec_ne_zero» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_live_of_segreVec_ne_zero_8419d5c16931
