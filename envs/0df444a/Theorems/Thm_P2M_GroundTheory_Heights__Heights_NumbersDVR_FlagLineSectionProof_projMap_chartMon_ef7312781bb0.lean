-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_projMap_chartMon_ef7312781bb0
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_projMap_chartMon_ef7312781bb0
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:49.927507+00:00
-- url     : https://prove2.me/theorems/4bf4d886-89d2-497d-81bd-b3a50f441983
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof proj Map chart Mon ef7312781bb0: P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof proj Map chart Mon ef73
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof proj Map chart Mon ef7312781bb0 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof proj Map chart Mon ef7312781bb0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineSectionForms.lean#L68-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineSectionForms.lean#L68-L72

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_projMap_chartMon_ef7312781bb0 (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) (c : ∀ k, ι k) (α : K → ℕ) :
    projMap F y w φ t (chartMon F M c α) =
      C (algebraMap Ω Φ (∏ k, y ⟨k, c k⟩ ^ α k)) * tMon α := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagLineSectionProof».«projMap_chartMon» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_projMap_chartMon_ef7312781bb0
