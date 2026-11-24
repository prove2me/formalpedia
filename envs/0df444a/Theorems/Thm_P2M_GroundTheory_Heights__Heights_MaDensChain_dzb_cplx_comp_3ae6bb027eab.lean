-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensChain_dzb_cplx_comp_3ae6bb027eab
-- name    : P2M_GroundTheory_Heights__Heights_MaDensChain_dzb_cplx_comp_3ae6bb027eab
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:52.452566+00:00
-- url     : https://prove2.me/theorems/bfbe75e2-6d2d-4958-8dad-d7720f1312f1
-- title:
--   P2 M Ground Theory Heights  Heights Ma Dens Chain dzb cplx comp 3ae6bb027eab: P2 M Ground Theory Heights  Heights Ma Dens Chain dzb cplx comp 3ae6bb027eab
-- statement:
--   The P2 M Ground Theory Heights  Heights Ma Dens Chain dzb cplx comp 3ae6bb027eab construction uses the P2 M Ground Theory Heights  Heights Ma Dens Chain dzb cplx comp 3ae6bb027eab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMaDensChain.lean#L30-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMaDensChain.lean#L30-L36

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

theorem P2M_GroundTheory_Heights__Heights_MaDensChain_dzb_cplx_comp_3ae6bb027eab (k : Fin D) (h : ℝ → ℝ) (g : (Fin D → ℂ) → ℝ) (y : Fin D → ℂ)
    (hh : DifferentiableAt ℝ h (g y)) (hg : DifferentiableAt ℝ g y) :
    dzb k (cplx (h ∘ g)) y = ((deriv h (g y) : ℝ) : ℂ) * dzb k (cplx g) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MaDensChain».«dzb_cplx_comp» := P2M_GroundTheory_Heights__Heights_MaDensChain_dzb_cplx_comp_3ae6bb027eab
