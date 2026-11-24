-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_IsChartForm_pad_50525580a2b7
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_IsChartForm_pad_50525580a2b7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:16.088501+00:00
-- url     : https://prove2.me/theorems/1b395842-e831-41cf-89e8-06744adcb7bc
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof Is Chart Form pad 50525580a2b7: P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof Is Chart Form pad 505255
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof Is Chart Form pad 50525580a2b7 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof Is Chart Form pad 50525580a2b7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineSectionForms.lean#L100-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineSectionForms.lean#L100-L111

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_IsChartForm_pad_50525580a2b7 {y : (Σ k, ι k) → Ω} {w : Module.Basis (Fin N) Ω E}
    {φ : Fin M → Module.Dual Ω E} {t : Fin N → Φ} {c : ∀ k, ι k} {a : Ω} {n : ℕ}
    {A : MRing (bundleIdx ι M) F} (h : IsChartForm F M y w φ t c a n A) (m : ℕ) :
    IsChartForm F M y w φ t c a (n + m) (A * chartMon F M c (fun _ => m)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagLineSectionProof».«IsChartForm».«pad» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_IsChartForm_pad_50525580a2b7
