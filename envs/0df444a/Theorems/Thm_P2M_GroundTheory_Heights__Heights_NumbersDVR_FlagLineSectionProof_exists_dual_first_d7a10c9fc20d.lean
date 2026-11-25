-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_exists_dual_first_d7a10c9fc20d
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_exists_dual_first_d7a10c9fc20d
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:30:14.764486+00:00
-- url     : https://prove2.me/theorems/8633922a-908e-434f-b7b8-8e4cde02db7c
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof exists dual first d7a10c9fc20d: P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof exists dual first d7a10c
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof exists dual first d7a10c9fc20d construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof exists dual first d7a10c9fc20d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineSectionSplit.lean#L27-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineSectionSplit.lean#L27-L114

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagLineSectionForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagLineSectionSplit
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
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type} {Ω : Type*} [Field Ω] {F : Type*} [Field F]
  [Algebra F Ω] {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_exists_dual_first_d7a10c9fc20d (y : (Σ k, ι k) → Ω) (B : ChartBundle F (segreVec y) N E)
    (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ) (hB : IsFlagFrame y B w b) (c : ∀ k, ι k)
    (hc : segreVec y c ≠ 0) (h0 : 0 < N) :
    ∃ ψ : Module.Dual Ω E, (∀ v ∈ B.lat c, ψ v ∈ chartRing F (segreVec y) c) ∧
      ψ (w ⟨0, h0⟩) * chartZ y c (b ⟨0, h0⟩) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagLineSectionProof».«exists_dual_first» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_exists_dual_first_d7a10c9fc20d
