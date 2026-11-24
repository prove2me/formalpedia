-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_chartLift_segre_apply_6eeb1c8817f9
-- name    : P2M_GroundTheory_Heights__Heights_chartLift_segre_apply_6eeb1c8817f9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:27.23014+00:00
-- url     : https://prove2.me/theorems/5a418ab2-91f9-4a23-894e-2161bb3e5960
-- title:
--   P2 M Ground Theory Heights  Heights chart Lift segre apply 6eeb1c8817f9: P2 M Ground Theory Heights  Heights chart Lift segre apply 6eeb1c8817f9
-- statement:
--   The P2 M Ground Theory Heights  Heights chart Lift segre apply 6eeb1c8817f9 construction uses the P2 M Ground Theory Heights  Heights chart Lift segre apply 6eeb1c8817f9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/SegreChartObjects.lean#L72-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/SegreChartObjects.lean#L72-L94

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
omit [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_chartLift_segre_apply_6eeb1c8817f9 {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (z : (Σ k, ι k) → ℂ) (hz : segre z i = 1) (k : K) (j : ι k) :
    chartLift σ i (fun a => segre z (σ a)) ⟨k, j⟩ = z ⟨k, j⟩ * (z ⟨k, i k⟩)⁻¹ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«chartLift_segre_apply» := P2M_GroundTheory_Heights__Heights_chartLift_segre_apply_6eeb1c8817f9
