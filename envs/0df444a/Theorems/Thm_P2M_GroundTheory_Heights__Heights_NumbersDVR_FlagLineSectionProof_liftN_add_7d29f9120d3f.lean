-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_liftN_add_7d29f9120d3f
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_liftN_add_7d29f9120d3f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:39.696365+00:00
-- url     : https://prove2.me/theorems/935eda3d-0cb8-4878-8849-b7b54e464ff0
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof lift N add 7d29f9120d3f: P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof lift N add 7d29f9120d3f
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof lift N add 7d29f9120d3f construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Section Proof lift N add 7d29f9120d3f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineSectionForms.lean#L36-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineSectionForms.lean#L36-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagLineSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagLineSectionForms
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
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagLineSectionProof
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type} {Ω : Type*} [Field Ω]
  {F : Type*} [Field F] [Algebra F Ω] {N M : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]
  {Φ : Type*} [Field Φ] [Algebra Ω Φ]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_liftN_add_7d29f9120d3f (α β : K → ℕ) : liftN (α + β) = liftN α + liftN β := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagLineSectionProof».«liftN_add» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_liftN_add_7d29f9120d3f
