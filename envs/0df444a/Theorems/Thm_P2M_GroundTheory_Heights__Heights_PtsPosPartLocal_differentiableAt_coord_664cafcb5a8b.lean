-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_differentiableAt_coord_664cafcb5a8b
-- name    : P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_differentiableAt_coord_664cafcb5a8b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:12:06.746293+00:00
-- url     : https://prove2.me/theorems/8ae8f815-7271-4787-82d9-b69c324c1242
-- title:
--   P2 M Ground Theory Heights  Heights Pts Pos Part Local differentiable At coord 664cafcb5a8b: P2 M Ground Theory Heights  Heights Pts Pos Part Local differentiable At coord 664cafcb5a8b
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Pos Part Local differentiable At coord 664cafcb5a8b construction uses the P2 M Ground Theory Heights  Heights Pts Pos Part Local differentiable At coord 664cafcb5a8b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsPosPartLocal.lean#L59-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsPosPartLocal.lean#L59-L62

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

theorem P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_differentiableAt_coord_664cafcb5a8b (w : ((k : K) → ι k) → ℂ) (i : Fin (e + 1)) :
    DifferentiableAt ℂ (fun x => Ψ x i) w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsPosPartLocal».«differentiableAt_coord» := P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_differentiableAt_coord_664cafcb5a8b
