-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensLeibniz_hessC_sq_half_d7954601c4d4
-- name    : P2M_GroundTheory_Heights__Heights_MaDensLeibniz_hessC_sq_half_d7954601c4d4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:34.115918+00:00
-- url     : https://prove2.me/theorems/5c193366-8cb4-4a87-9648-afb1a6cf3093
-- title:
--   P2 M Ground Theory Heights  Heights Ma Dens Leibniz hess C sq half d7954601c4d4: P2 M Ground Theory Heights  Heights Ma Dens Leibniz hess C sq half d7954601c4d4
-- statement:
--   The P2 M Ground Theory Heights  Heights Ma Dens Leibniz hess C sq half d7954601c4d4 construction uses the P2 M Ground Theory Heights  Heights Ma Dens Leibniz hess C sq half d7954601c4d4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMaDensLeibniz.lean#L66-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMaDensLeibniz.lean#L66-L79

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryParts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensLeibniz
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
open GroundTheory.Heights₂.Heights.MaDensLeibniz
variable {D : ℕ}

theorem P2M_GroundTheory_Heights__Heights_MaDensLeibniz_hessC_sq_half_d7954601c4d4 (f : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hf : ContDiffAt ℝ 2 f z) :
    hessC (fun y => f y ^ 2 / 2) z = (f z : ℂ) • hessC f z + gradMat f f z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MaDensLeibniz».«hessC_sq_half» := P2M_GroundTheory_Heights__Heights_MaDensLeibniz_hessC_sq_half_d7954601c4d4
