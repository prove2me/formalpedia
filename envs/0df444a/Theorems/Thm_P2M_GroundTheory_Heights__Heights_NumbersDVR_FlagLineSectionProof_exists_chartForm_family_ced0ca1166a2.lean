-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_exists_chartForm_family_ced0ca1166a2
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_exists_chartForm_family_ced0ca1166a2
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:30:09.216494+00:00
-- url     : https://prove2.me/theorems/86fb4446-2b9d-484c-9121-4cbf92cd4c56
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof exists chart Form family ced0ca1166a2: P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof exists chart Form
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof exists chart Form family ced0ca1166a2 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof exists chart Form family ced0ca1166a2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineSectionForms.lean#L152-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineSectionForms.lean#L152-L161

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_exists_chartForm_family_ced0ca1166a2 (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) (c : ∀ k, ι k) (hc : segreVec y c ≠ 0)
    {J : Type*} [Fintype J] (a : J → Ω) (ha : ∀ j, a j ∈ chartRing F (segreVec y) c) :
    ∃ n : ℕ, ∀ m, n ≤ m → ∀ j, ∃ A : MRing (bundleIdx ι M) F, IsChartForm F M y w φ t c (a j) m A := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagLineSectionProof».«exists_chartForm_family» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_exists_chartForm_family_ced0ca1166a2
