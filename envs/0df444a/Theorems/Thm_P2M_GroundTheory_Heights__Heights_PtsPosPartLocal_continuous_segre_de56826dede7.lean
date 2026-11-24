-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_continuous_segre_de56826dede7
-- name    : P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_continuous_segre_de56826dede7
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:19.162937+00:00
-- url     : https://prove2.me/theorems/91d41e2e-5bf3-4263-8da5-d34bd9e81ec4
-- title:
--   P2 M Ground Theory Heights  Heights Pts Pos Part Local continuous segre de56826dede7: P2 M Ground Theory Heights  Heights Pts Pos Part Local continuous segre de56826dede7
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Pos Part Local continuous segre de56826dede7 construction uses the P2 M Ground Theory Heights  Heights Pts Pos Part Local continuous segre de56826dede7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsPosPartLocal.lean#L77-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsPosPartLocal.lean#L77-L78

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsPosPartLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsPosPartLocal
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
open MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.PtsPosPartLocal
set_option linter.unusedSectionVars false
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}
variable {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}

theorem P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_continuous_segre_de56826dede7 : Continuous (segre : ((Σ k, ι k) → ℂ) → ((k : K) → ι k) → ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsPosPartLocal».«continuous_segre» := P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_continuous_segre_de56826dede7
