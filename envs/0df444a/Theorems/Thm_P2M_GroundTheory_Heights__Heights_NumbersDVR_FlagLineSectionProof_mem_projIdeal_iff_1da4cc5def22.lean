-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_mem_projIdeal_iff_1da4cc5def22
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_mem_projIdeal_iff_1da4cc5def22
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:31:50.452837+00:00
-- url     : https://prove2.me/theorems/cdaa1e78-f0e2-4083-b620-1a0496f8a3c7
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof mem proj Ideal iff 1da4cc5def22: P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof mem proj Ideal iff 1da4
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof mem proj Ideal iff 1da4cc5def22 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof mem proj Ideal iff 1da4cc5def22 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineSectionForms.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineSectionForms.lean#L24-L27

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_mem_projIdeal_iff_1da4cc5def22 {y : (Σ k, ι k) → Ω} {w : Module.Basis (Fin N) Ω E}
    {φ : Fin M → Module.Dual Ω E} {t : Fin N → Φ} {h : MRing (bundleIdx ι M) F} :
    h ∈ projIdeal F y w φ t ↔ projMap F y w φ t h = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagLineSectionProof».«mem_projIdeal_iff» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_mem_projIdeal_iff_1da4cc5def22
