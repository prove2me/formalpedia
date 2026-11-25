-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_eval_trunc_eq_zero_eec4abf02011
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_eval_trunc_eq_zero_eec4abf02011
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:07:53.224035+00:00
-- url     : https://prove2.me/theorems/c34c55ab-936d-424f-80d6-523dfe966477
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section eval trunc eq zero eec4abf02011: P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section eval trunc eq zero
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section eval trunc eq zero eec4abf02011 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section eval trunc eq zero eec4abf02011 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleChartSectionTools.lean#L297-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleChartSectionTools.lean#L297-L323

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleChartSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleSectionFormsTools
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PProjIdealFormValue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleChartSectionTools
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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_eval_trunc_eq_zero_eec4abf02011 (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) {t : Fin N → Φ} (ht : AlgebraicIndependent Ω t) (i : ℕ)
    {q : MRing (bundleIdx ι M) F} (hq : q ∈ projIdeal F y w φ (truncCoord t i)) (τ : Fin N → Φ) :
    eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord τ i)) q = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagBundleChartSection».«eval_trunc_eq_zero» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_eval_trunc_eq_zero_eec4abf02011
