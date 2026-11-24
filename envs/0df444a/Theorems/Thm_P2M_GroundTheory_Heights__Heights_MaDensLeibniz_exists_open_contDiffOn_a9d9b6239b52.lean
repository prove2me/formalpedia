-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensLeibniz_exists_open_contDiffOn_a9d9b6239b52
-- name    : P2M_GroundTheory_Heights__Heights_MaDensLeibniz_exists_open_contDiffOn_a9d9b6239b52
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:47.148705+00:00
-- url     : https://prove2.me/theorems/6bab0c86-06b2-4d4d-a0fe-124e4c073554
-- title:
--   P2 M Ground Theory Heights  Heights Ma Dens Leibniz exists open cont Diff On a9d9b6239b52: P2 M Ground Theory Heights  Heights Ma Dens Leibniz exists open cont Diff On a9d9b6239b52
-- statement:
--   The P2 M Ground Theory Heights  Heights Ma Dens Leibniz exists open cont Diff On a9d9b6239b52 construction uses the P2 M Ground Theory Heights  Heights Ma Dens Leibniz exists open cont Diff On a9d9b6239b52 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMaDensLeibniz.lean#L16-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMaDensLeibniz.lean#L16-L22

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

theorem P2M_GroundTheory_Heights__Heights_MaDensLeibniz_exists_open_contDiffOn_a9d9b6239b52 (f g : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hf : ContDiffAt ℝ 2 f z)
    (hg : ContDiffAt ℝ 2 g z) :
    ∃ U : Set (Fin D → ℂ), IsOpen U ∧ z ∈ U ∧ ContDiffOn ℝ 2 f U ∧ ContDiffOn ℝ 2 g U := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MaDensLeibniz».«exists_open_contDiffOn» := P2M_GroundTheory_Heights__Heights_MaDensLeibniz_exists_open_contDiffOn_a9d9b6239b52
