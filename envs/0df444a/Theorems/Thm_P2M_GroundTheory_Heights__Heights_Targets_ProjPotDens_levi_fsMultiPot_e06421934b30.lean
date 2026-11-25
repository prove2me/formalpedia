-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_levi_fsMultiPot_e06421934b30
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_levi_fsMultiPot_e06421934b30
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:34:11.174819+00:00
-- url     : https://prove2.me/theorems/d7db8b4b-7e4d-4005-89c9-1477bcbddb53
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Pot Dens levi fs Multi Pot e06421934b30: P2 M Ground Theory Heights  Heights Targets Proj Pot Dens levi fs Multi Pot e06421934b30
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Pot Dens levi fs Multi Pot e06421934b30 construction uses the P2 M Ground Theory Heights  Heights Targets Proj Pot Dens levi fs Multi Pot e06421934b30 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjPotDensLevi.lean#L67-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjPotDensLevi.lean#L67-L111

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_FsMetricFinIsSemipositive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotDensLevi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open GroundTheory.Heights₂.Heights.Targets.ProjPotDens
open ReciprocityTheory.AnForm ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_levi_fsMultiPot_e06421934b30 (p : (k : K) → ι k) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, z ⟨k, p k⟩ ≠ 0) (v : (Σ k, ι k) → ℂ) :
    ContDiffAt ℝ 2 fsMultiPot z ∧ 0 ≤ levi fsMultiPot z v ∧
      ((∀ k, v ⟨k, p k⟩ = 0) → v ≠ 0 → 0 < levi fsMultiPot z v) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjPotDens».«levi_fsMultiPot» := P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_levi_fsMultiPot_e06421934b30
