-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensChain_fderiv_comp_real_7cfce8fb8fcd
-- name    : P2M_GroundTheory_Heights__Heights_MaDensChain_fderiv_comp_real_7cfce8fb8fcd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:47.940605+00:00
-- url     : https://prove2.me/theorems/ec672811-aa95-4846-8b65-5f7ebe671368
-- title:
--   P2 M Ground Theory Heights  Heights Ma Dens Chain fderiv comp real 7cfce8fb8fcd: P2 M Ground Theory Heights  Heights Ma Dens Chain fderiv comp real 7cfce8fb8fcd
-- statement:
--   The P2 M Ground Theory Heights  Heights Ma Dens Chain fderiv comp real 7cfce8fb8fcd construction uses the P2 M Ground Theory Heights  Heights Ma Dens Chain fderiv comp real 7cfce8fb8fcd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMaDensChain.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMaDensChain.lean#L17-L20

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMaDensChain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensLeibniz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensChain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.MaDensChain
variable {D : ℕ}

theorem P2M_GroundTheory_Heights__Heights_MaDensChain_fderiv_comp_real_7cfce8fb8fcd (h : ℝ → ℝ) (g : (Fin D → ℂ) → ℝ) (y : Fin D → ℂ)
    (hh : DifferentiableAt ℝ h (g y)) (hg : DifferentiableAt ℝ g y) :
    fderiv ℝ (h ∘ g) y = deriv h (g y) • fderiv ℝ g y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MaDensChain».«fderiv_comp_real» := P2M_GroundTheory_Heights__Heights_MaDensChain_fderiv_comp_real_7cfce8fb8fcd
