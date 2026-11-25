-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_chartWeight_of_coord_6d29224d3334
-- name    : P2M_GroundTheory_Heights__Heights_chartWeight_of_coord_6d29224d3334
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:09:38.303139+00:00
-- url     : https://prove2.me/theorems/e4bb233a-df09-41e9-ba8b-cef25d3b6a0d
-- title:
--   P2 M Ground Theory Heights  Heights chart Weight of coord 6d29224d3334: P2 M Ground Theory Heights  Heights chart Weight of coord 6d29224d3334
-- statement:
--   The P2 M Ground Theory Heights  Heights chart Weight of coord 6d29224d3334 construction uses the P2 M Ground Theory Heights  Heights chart Weight of coord 6d29224d3334 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/SegreChartProjObjects.lean#L75-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/SegreChartProjObjects.lean#L75-L78

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_SegreChartObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_SegreChartProjObjects
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
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm pot segre)
open ComplexSets Matrix
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_chartWeight_of_coord_6d29224d3334 {m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)} {i : (k : K) → ι k}
    (g : ((Σ k, ι k) → ℂ) → ℝ) {x : Fin m → ℂ} (hx : x (σ.symm i) = 1) :
    chartWeight σ i g x = g (chartLift σ i x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«chartWeight_of_coord» := P2M_GroundTheory_Heights__Heights_chartWeight_of_coord_6d29224d3334
