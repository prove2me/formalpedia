-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensChain_hessC_comp_real_1b578ed93f88
-- name    : P2M_GroundTheory_Heights__Heights_MaDensChain_hessC_comp_real_1b578ed93f88
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:34.982289+00:00
-- url     : https://prove2.me/theorems/79d50ad7-5e3d-49da-8a5a-41aa1f38c163
-- title:
--   P2 M Ground Theory Heights  Heights Ma Dens Chain hess C comp real 1b578ed93f88: P2 M Ground Theory Heights  Heights Ma Dens Chain hess C comp real 1b578ed93f88
-- statement:
--   The P2 M Ground Theory Heights  Heights Ma Dens Chain hess C comp real 1b578ed93f88 construction uses the P2 M Ground Theory Heights  Heights Ma Dens Chain hess C comp real 1b578ed93f88 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMaDensChain.lean#L38-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMaDensChain.lean#L38-L61

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

theorem P2M_GroundTheory_Heights__Heights_MaDensChain_hessC_comp_real_1b578ed93f88 (F : ℝ → ℝ) (g : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hF : ContDiff ℝ 2 F)
    (hg : ContDiffAt ℝ 2 g z) :
    hessC (F ∘ g) z = ((deriv F (g z) : ℝ) : ℂ) • hessC g z + ((deriv (deriv F) (g z) : ℝ) : ℂ) • gradMat g g z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MaDensChain».«hessC_comp_real» := P2M_GroundTheory_Heights__Heights_MaDensChain_hessC_comp_real_1b578ed93f88
