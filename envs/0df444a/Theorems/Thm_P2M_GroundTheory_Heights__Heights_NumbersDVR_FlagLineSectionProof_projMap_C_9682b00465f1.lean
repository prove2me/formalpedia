-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_projMap_C_9682b00465f1
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_projMap_C_9682b00465f1
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:06:25.242806+00:00
-- url     : https://prove2.me/theorems/dc1b9986-5346-4321-93fe-12aa0fe84ada
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof proj Map C 9682b00465f1: P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof proj Map C 9682b00465f1
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof proj Map C 9682b00465f1 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof proj Map C 9682b00465f1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineSectionForms.lean#L63-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineSectionForms.lean#L63-L66

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_projMap_C_9682b00465f1 (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) (r : F) :
    projMap F y w φ t (C r) = C (algebraMap Ω Φ (algebraMap F Ω r)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagLineSectionProof».«projMap_C» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_projMap_C_9682b00465f1
