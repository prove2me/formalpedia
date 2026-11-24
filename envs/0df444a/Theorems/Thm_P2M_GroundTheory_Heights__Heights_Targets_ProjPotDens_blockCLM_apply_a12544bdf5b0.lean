-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_blockCLM_apply_a12544bdf5b0
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_blockCLM_apply_a12544bdf5b0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:53:41.334683+00:00
-- url     : https://prove2.me/theorems/ccd29751-adf2-4327-b387-67aa612740fd
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Pot Dens block CLM apply a12544bdf5b0: P2 M Ground Theory Heights  Heights Targets Proj Pot Dens block CLM apply a12544bdf5b0
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Pot Dens block CLM apply a12544bdf5b0 construction uses the P2 M Ground Theory Heights  Heights Targets Proj Pot Dens block CLM apply a12544bdf5b0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjPotDensLevi.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjPotDensLevi.lean#L20-L21

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
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_blockCLM_apply_a12544bdf5b0 (k : K) (z : (Σ k, ι k) → ℂ) (i : ι k) :
    blockCLM k z i = z ⟨k, i⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjPotDens».«blockCLM_apply» := P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_blockCLM_apply_a12544bdf5b0

attribute [defeq] P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_blockCLM_apply_a12544bdf5b0
