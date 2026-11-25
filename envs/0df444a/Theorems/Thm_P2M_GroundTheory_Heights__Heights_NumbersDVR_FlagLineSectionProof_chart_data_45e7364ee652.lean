-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_chart_data_45e7364ee652
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_chart_data_45e7364ee652
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:30:50.025259+00:00
-- url     : https://prove2.me/theorems/b8e39665-c598-4844-884e-65785f776888
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof chart data 45e7364ee652: P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof chart data 45e7364ee652
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof chart data 45e7364ee652 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof chart data 45e7364ee652 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineSectionSplit.lean#L116-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineSectionSplit.lean#L116-L156

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_chart_data_45e7364ee652 (y : (Σ k, ι k) → Ω) (B : ChartBundle F (segreVec y) N E)
    (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ) (hB : IsFlagFrame y B w b) {M : ℕ}
    (a : K → ℤ) (φ : Fin M → Module.Dual Ω E) (hφ : IsTwistedDualGens y B a φ) (c : ∀ k, ι k)
    (hc : segreVec y c ≠ 0) (h0 : 0 < N) :
    (∀ l, φ l (w ⟨0, h0⟩) * chartZ y c (b ⟨0, h0⟩ - a) ∈ chartRing F (segreVec y) c) ∧
      ∃ v : Fin M → Ω, (∀ l, v l ∈ chartRing F (segreVec y) c) ∧
        ∑ l, v l * (φ l (w ⟨0, h0⟩) * chartZ y c (b ⟨0, h0⟩ - a)) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagLineSectionProof».«chart_data» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_chart_data_45e7364ee652
