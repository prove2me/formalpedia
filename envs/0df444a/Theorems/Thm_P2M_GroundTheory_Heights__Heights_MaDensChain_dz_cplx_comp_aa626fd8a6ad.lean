-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensChain_dz_cplx_comp_aa626fd8a6ad
-- name    : P2M_GroundTheory_Heights__Heights_MaDensChain_dz_cplx_comp_aa626fd8a6ad
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:02.420999+00:00
-- url     : https://prove2.me/theorems/e2df97c1-7957-464b-861b-4316c846fd67
-- title:
--   P2 M Ground Theory Heights  Heights Ma Dens Chain dz cplx comp aa626fd8a6ad: P2 M Ground Theory Heights  Heights Ma Dens Chain dz cplx comp aa626fd8a6ad
-- statement:
--   The P2 M Ground Theory Heights  Heights Ma Dens Chain dz cplx comp aa626fd8a6ad construction uses the P2 M Ground Theory Heights  Heights Ma Dens Chain dz cplx comp aa626fd8a6ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMaDensChain.lean#L22-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMaDensChain.lean#L22-L28

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

theorem P2M_GroundTheory_Heights__Heights_MaDensChain_dz_cplx_comp_aa626fd8a6ad (j : Fin D) (h : ℝ → ℝ) (g : (Fin D → ℂ) → ℝ) (y : Fin D → ℂ)
    (hh : DifferentiableAt ℝ h (g y)) (hg : DifferentiableAt ℝ g y) :
    dz j (cplx (h ∘ g)) y = ((deriv h (g y) : ℝ) : ℂ) * dz j (cplx g) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MaDensChain».«dz_cplx_comp» := P2M_GroundTheory_Heights__Heights_MaDensChain_dz_cplx_comp_aa626fd8a6ad
