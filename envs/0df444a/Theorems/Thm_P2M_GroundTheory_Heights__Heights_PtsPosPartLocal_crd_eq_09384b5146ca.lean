-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_crd_eq_09384b5146ca
-- name    : P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_crd_eq_09384b5146ca
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:30.868745+00:00
-- url     : https://prove2.me/theorems/355262c9-4a01-437c-98c5-3d2871c23578
-- title:
--   P2 M Ground Theory Heights  Heights Pts Pos Part Local crd eq 09384b5146ca: P2 M Ground Theory Heights  Heights Pts Pos Part Local crd eq 09384b5146ca
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Pos Part Local crd eq 09384b5146ca construction uses the P2 M Ground Theory Heights  Heights Pts Pos Part Local crd eq 09384b5146ca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsPosPartLocal.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsPosPartLocal.lean#L27-L29

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

theorem P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_crd_eq_09384b5146ca (w : ((k : K) → ι k) → ℂ) : crd Ψ w = fun i => (Ψ w 0)⁻¹ * Ψ w i.succ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsPosPartLocal».«crd_eq» := P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_crd_eq_09384b5146ca
