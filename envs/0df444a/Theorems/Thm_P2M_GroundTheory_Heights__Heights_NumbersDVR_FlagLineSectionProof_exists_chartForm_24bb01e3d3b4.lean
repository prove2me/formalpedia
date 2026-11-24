-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_exists_chartForm_24bb01e3d3b4
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_exists_chartForm_24bb01e3d3b4
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:48.333196+00:00
-- url     : https://prove2.me/theorems/4d18c553-9e38-4be5-85bc-73251134bd23
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof exists chart Form 24bb01e3d3b4: P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof exists chart Form 24bb01
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof exists chart Form 24bb01e3d3b4 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof exists chart Form 24bb01e3d3b4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineSectionForms.lean#L113-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineSectionForms.lean#L113-L150

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_exists_chartForm_24bb01e3d3b4 (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) (c : ∀ k, ι k) (hc : segreVec y c ≠ 0)
    {a : Ω} (ha : a ∈ chartRing F (segreVec y) c) :
    ∃ (n : ℕ) (A : MRing (bundleIdx ι M) F), IsChartForm F M y w φ t c a n A := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagLineSectionProof».«exists_chartForm» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_exists_chartForm_24bb01e3d3b4
