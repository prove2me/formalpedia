-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_apply_eq_of_segre_eq_0b2426e6d1f1
-- name    : P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_apply_eq_of_segre_eq_0b2426e6d1f1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:11:39.226175+00:00
-- url     : https://prove2.me/theorems/4605f5c4-65c7-49c5-a9ff-d944ac783671
-- title:
--   P2 M Ground Theory Heights  Heights Pts Pos Part Local apply eq of segre eq 0b2426e6d1f1: P2 M Ground Theory Heights  Heights Pts Pos Part Local apply eq of segre eq 0b2426e6d1f1
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Pos Part Local apply eq of segre eq 0b2426e6d1f1 construction uses the P2 M Ground Theory Heights  Heights Pts Pos Part Local apply eq of segre eq 0b2426e6d1f1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsPosPartLocal.lean#L86-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsPosPartLocal.lean#L86-L92

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

theorem P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_apply_eq_of_segre_eq_0b2426e6d1f1 {β : Sort*} {F : ((Σ k, ι k) → ℂ) → β}
    (hF : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → F (fun p => c p.1 * z p) = F z)
    {u v : (Σ k, ι k) → ℂ} (hu : ∀ k, ∃ i, u ⟨k, i⟩ ≠ 0) (h : segre u = segre v) : F v = F u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsPosPartLocal».«apply_eq_of_segre_eq» := P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_apply_eq_of_segre_eq_0b2426e6d1f1
