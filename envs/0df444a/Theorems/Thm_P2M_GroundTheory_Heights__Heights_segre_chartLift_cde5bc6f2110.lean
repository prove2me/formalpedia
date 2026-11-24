-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_segre_chartLift_cde5bc6f2110
-- name    : P2M_GroundTheory_Heights__Heights_segre_chartLift_cde5bc6f2110
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:45.199451+00:00
-- url     : https://prove2.me/theorems/198389c4-a8d5-4485-9044-2e78fb88b9dc
-- title:
--   P2 M Ground Theory Heights  Heights segre chart Lift cde5bc6f2110: P2 M Ground Theory Heights  Heights segre chart Lift cde5bc6f2110
-- statement:
--   The P2 M Ground Theory Heights  Heights segre chart Lift cde5bc6f2110 construction uses the P2 M Ground Theory Heights  Heights segre chart Lift cde5bc6f2110 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/SegreChartObjects.lean#L96-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/SegreChartObjects.lean#L96-L103

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

theorem P2M_GroundTheory_Heights__Heights_segre_chartLift_cde5bc6f2110 {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (z : (Σ k, ι k) → ℂ) (hz : segre z i = 1) :
    segre (chartLift σ i (fun a => segre z (σ a))) = segre z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«segre_chartLift» := P2M_GroundTheory_Heights__Heights_segre_chartLift_cde5bc6f2110
