-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_exists_section_form_0be7fabf5a7b
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_exists_section_form_0be7fabf5a7b
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:06:36.358585+00:00
-- url     : https://prove2.me/theorems/9c4abd84-de14-45d4-9c3c-f079c169e11a
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section exists section form 0be7fabf5a7b: P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section exists section for
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section exists section form 0be7fabf5a7b construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section exists section form 0be7fabf5a7b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleChartSectionTools.lean#L402-L496
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleChartSectionTools.lean#L402-L496

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_exists_section_form_0be7fabf5a7b (y : (Σ k, ι k) → Ω) (B : ChartBundle F (segreVec y) N E)
    (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ) (hfl : IsFlagFrame y B w b) (a : K → ℤ)
    (φ : Fin M → Module.Dual Ω E) (hφ : IsTwistedDualGens y B a φ) (t : Fin N → Φ) (i : Fin N)
    (c : ∀ k, ι k) (hsc : segreVec y c ≠ 0) :
    ∃ (dl : Option K → ℕ) (β : K → ℕ) (f : MRing (bundleIdx ι M) F), IsMultiHomog f dl ∧
      (fun o => (dl o : ℤ) - liftNat β o) = zetaDeg + liftDeg (b i - a) ∧
      eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) f =
        t i * eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω))
          (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) (chartMono M c β) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagBundleChartSection».«exists_section_form» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_exists_section_form_0be7fabf5a7b
