-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_component_mem_projIdeal_cedf5a28dfa6
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_component_mem_projIdeal_cedf5a28dfa6
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:05:48.579059+00:00
-- url     : https://prove2.me/theorems/edaf9416-52ef-42e1-aaff-d87a5d0634cf
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section component mem proj Ideal cedf5a28dfa6: P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section component mem
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section component mem proj Ideal cedf5a28dfa6 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Chart Section component mem proj Ideal cedf5a28dfa6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleChartSectionTools.lean#L278-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleChartSectionTools.lean#L278-L295

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_component_mem_projIdeal_cedf5a28dfa6 (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) {q : MRing (bundleIdx ι M) F}
    (hq : q ∈ projIdeal F y w φ t) (d : Option K → ℕ) :
    weightedHomogeneousComponent (blockWeight (bundleIdx ι M)) d q ∈ projIdeal F y w φ t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagBundleChartSection».«component_mem_projIdeal» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_component_mem_projIdeal_cedf5a28dfa6
