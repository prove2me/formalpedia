-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_eval_eq_zero_of_mem_projIdeal_423451969e42
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_eval_eq_zero_of_mem_projIdeal_423451969e42
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:12:25.396429+00:00
-- url     : https://prove2.me/theorems/ba004c0b-7313-5f58-b73c-a19f02a6a80c
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section eval eq zero of mem proj Ideal 423451969e42: P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section eval eq
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section eval eq zero of mem proj Ideal 423451969e42 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section eval eq zero of mem proj Ideal 423451969e42 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleChartSectionTools.lean#L258-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleChartSectionTools.lean#L258-L270

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleChartSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleSectionFormsTools
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PProjIdealFormValue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleChartSectionTools
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_eval_eq_zero_of_mem_projIdeal_77c3761ef824

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
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundleChartSection
open FlagBundleSectionForms (chartPow chartMono liftNat)
variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]
  {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
variable {M N : ℕ} {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_eval_eq_zero_of_mem_projIdeal_423451969e42 (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) {f : MRing (bundleIdx ι M) F}
    (hf : f ∈ projIdeal F y w φ t) :
    eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ t) f = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagBundleChartSection».«eval_eq_zero_of_mem_projIdeal» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_eval_eq_zero_of_mem_projIdeal_423451969e42
