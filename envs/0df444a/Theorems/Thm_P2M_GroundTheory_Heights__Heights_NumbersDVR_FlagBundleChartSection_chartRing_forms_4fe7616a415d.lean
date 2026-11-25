-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_chartRing_forms_4fe7616a415d
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_chartRing_forms_4fe7616a415d
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:06:37.132885+00:00
-- url     : https://prove2.me/theorems/b4fa82e8-407d-4bd1-89c7-75c30260b2a6
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section chart Ring forms 4fe7616a415d: P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section chart Ring forms 4fe7
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section chart Ring forms 4fe7616a415d construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section chart Ring forms 4fe7616a415d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleChartSectionTools.lean#L193-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleChartSectionTools.lean#L193-L236

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleChartSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleSectionFormsTools
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PProjIdealFormValue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleChartSectionTools
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_chartRing_forms_a08c172c2f9a

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_chartRing_forms_4fe7616a415d (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) (c : ∀ k, ι k) (hc : segreVec y c ≠ 0) {u : Ω}
    (hu : u ∈ chartRing F (segreVec y) c) :
    ∃ (n : ℕ) (U : MRing (bundleIdx ι M) F), IsMultiHomog U (liftNat fun _ => n) ∧
      eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ t) U =
        algebraMap Ω Φ (u * segreVec y c ^ n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagBundleChartSection».«chartRing_forms» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_chartRing_forms_4fe7616a415d
