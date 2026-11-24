-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_exists_flag_dual_ed946381b07c
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_exists_flag_dual_ed946381b07c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:55:19.819521+00:00
-- url     : https://prove2.me/theorems/664732de-23e8-48e9-ba6d-1b8947ccd5c4
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Section Forms exists flag dual ed946381b07c: P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Section Forms exists flag dual ed94
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Section Forms exists flag dual ed946381b07c construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Section Forms exists flag dual ed946381b07c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleSectionFormsTools.lean#L41-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleSectionFormsTools.lean#L41-L150

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
variable {N : ℕ} {E : Type} [AddCommGroup E] [Module Ω E]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_exists_flag_dual_ed946381b07c (y : (Σ k, ι k) → Ω) (B : ChartBundle F (segreVec y) N E)
    (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ) (hfl : IsFlagFrame y B w b)
    (c : ∀ k, ι k) (hc : segreVec y c ≠ 0) (i : Fin N) :
    ∃ ψ : Module.Dual Ω E, (∀ v ∈ B.lat c, ψ v ∈ chartRing F (segreVec y) c) ∧
      (∀ j, j < i → ψ (w j) = 0) ∧ ψ (w i) = (chartPow y c (b i))⁻¹ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagBundleSectionForms».«exists_flag_dual» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_exists_flag_dual_ed946381b07c
