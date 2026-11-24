-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_exists_adapted_77e9c8dbc8e4
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_exists_adapted_77e9c8dbc8e4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:49.618563+00:00
-- url     : https://prove2.me/theorems/931fb62e-bc12-4859-a61d-109c4fb80ba7
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof exists adapted 77e9c8dbc8e4: P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof exists adapted 77e9c8dbc8e4
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof exists adapted 77e9c8dbc8e4 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof exists adapted 77e9c8dbc8e4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineSectionSplit.lean#L18-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineSectionSplit.lean#L18-L25

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_exists_adapted_77e9c8dbc8e4 (y : (Σ k, ι k) → Ω) (B : ChartBundle F (segreVec y) N E)
    (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ) (hB : IsFlagFrame y B w b) (c : ∀ k, ι k)
    (hc : segreVec y c ≠ 0) (i : Fin N) :
    ∃ v ∈ B.lat c, (∀ j, i < j → w.repr v j = 0) ∧ w.repr v i = chartZ y c (b i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagLineSectionProof».«exists_adapted» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_exists_adapted_77e9c8dbc8e4
