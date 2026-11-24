-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_chartLift_blockNonzero_4a49d0f77c5b
-- name    : P2M_GroundTheory_Heights__Heights_chartLift_blockNonzero_4a49d0f77c5b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:02.416787+00:00
-- url     : https://prove2.me/theorems/e3d540f0-bdad-495c-be16-c224ceba3243
-- title:
--   P2 M Ground Theory Heights  Heights chart Lift block Nonzero 4a49d0f77c5b: P2 M Ground Theory Heights  Heights chart Lift block Nonzero 4a49d0f77c5b
-- statement:
--   The P2 M Ground Theory Heights  Heights chart Lift block Nonzero 4a49d0f77c5b construction uses the P2 M Ground Theory Heights  Heights chart Lift block Nonzero 4a49d0f77c5b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/SegreChartObjects.lean#L66-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/SegreChartObjects.lean#L66-L68

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StokesObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_SegreChartObjects
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo (MRing mcPts segre PBlk)
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_chartLift_blockNonzero_4a49d0f77c5b {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    {x : Fin m → ℂ} (hx : x (σ.symm i) = 1) : ∀ k, ∃ j, chartLift σ i x ⟨k, j⟩ ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«chartLift_blockNonzero» := P2M_GroundTheory_Heights__Heights_chartLift_blockNonzero_4a49d0f77c5b
