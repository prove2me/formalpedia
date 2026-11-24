-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_eval_eq_zero_of_mem_projIdeal_77c3761ef824
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_eval_eq_zero_of_mem_projIdeal_77c3761ef824
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:55:42.034254+00:00
-- url     : https://prove2.me/theorems/c0395156-83bf-4fcc-9904-67e41fb9591c
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Section Forms eval eq zero of mem proj Ideal 77c3761ef824: P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Section Forms eval eq
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Section Forms eval eq zero of mem proj Ideal 77c3761ef824 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Section Forms eval eq zero of mem proj Ideal 77c3761ef824 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleSectionFormsTools.lean#L228-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleSectionFormsTools.lean#L228-L240

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleSectionFormsTools
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
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundleSectionForms
variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]
  {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {M N : ℕ} {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_eval_eq_zero_of_mem_projIdeal_77c3761ef824 (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) {f : MRing (bundleIdx ι M) F}
    (hf : f ∈ projIdeal F y w φ t) :
    eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ t) f = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagBundleSectionForms».«eval_eq_zero_of_mem_projIdeal» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_eval_eq_zero_of_mem_projIdeal_77c3761ef824
