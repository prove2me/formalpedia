-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_segreVec_pow_851cfbba86d7
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_segreVec_pow_851cfbba86d7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:55:38.668244+00:00
-- url     : https://prove2.me/theorems/2302d1e9-5ba6-425f-8fa8-6ebb0f2f40fb
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Section Forms segre Vec pow 851cfbba86d7: P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Section Forms segre Vec pow 851cfbba86
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Section Forms segre Vec pow 851cfbba86d7 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Section Forms segre Vec pow 851cfbba86d7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleSectionFormsTools.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleSectionFormsTools.lean#L33-L35

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_segreVec_pow_851cfbba86d7 (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (n : ℕ) :
    segreVec y c ^ n = chartPow y c (fun _ => (n : ℤ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagBundleSectionForms».«segreVec_pow» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_segreVec_pow_851cfbba86d7
