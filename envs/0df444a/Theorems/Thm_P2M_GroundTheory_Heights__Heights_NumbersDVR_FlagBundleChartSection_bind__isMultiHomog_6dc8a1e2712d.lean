-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_bind__isMultiHomog_6dc8a1e2712d
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_bind__isMultiHomog_6dc8a1e2712d
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:06:01.298278+00:00
-- url     : https://prove2.me/theorems/6c6d52e8-0406-4689-ae19-3910a11f07d9
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section bind  is Multi Homog 6dc8a1e2712d: P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section bind  is Multi Ho
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section bind  is Multi Homog 6dc8a1e2712d construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section bind  is Multi Homog 6dc8a1e2712d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleChartSectionTools.lean#L328-L359
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleChartSectionTools.lean#L328-L359

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_bind__isMultiHomog_6dc8a1e2712d (g : (Σ o, bundleIdx ι M o) → MRing (bundleIdx ι M) F) (e : Option K → ℕ)
    (hs : ∀ k (p : ι k), g ⟨some k, p⟩ = X ⟨some k, p⟩) (hn : ∀ l, IsMultiHomog (g ⟨none, l⟩) e)
    {q : MRing (bundleIdx ι M) F} {d : Option K → ℕ} (hq : IsMultiHomog q d) :
    IsMultiHomog (bind₁ g q) (substDeg e d) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagBundleChartSection».«bind₁_isMultiHomog» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_bind__isMultiHomog_6dc8a1e2712d
