-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_chartRing_forms_fin_d2144ac6ed55
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_chartRing_forms_fin_d2144ac6ed55
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:15.112164+00:00
-- url     : https://prove2.me/theorems/39f6eaa7-1cd2-40d5-8ffa-49627af467df
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section chart Ring forms fin d2144ac6ed55: P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section chart Ring forms
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section chart Ring forms fin d2144ac6ed55 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section chart Ring forms fin d2144ac6ed55 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleChartSectionTools.lean#L238-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleChartSectionTools.lean#L238-L256

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_chartRing_forms_fin_d2144ac6ed55 (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) (c : ∀ k, ι k) (hc : segreVec y c ≠ 0) {L : ℕ}
    {u : Fin L → Ω} (hu : ∀ l, u l ∈ chartRing F (segreVec y) c) :
    ∃ (n : ℕ) (U : Fin L → MRing (bundleIdx ι M) F), (∀ l, IsMultiHomog (U l) (liftNat fun _ => n)) ∧
      ∀ l, eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ t) (U l) =
        algebraMap Ω Φ (u l * segreVec y c ^ n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagBundleChartSection».«chartRing_forms_fin» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_chartRing_forms_fin_d2144ac6ed55
