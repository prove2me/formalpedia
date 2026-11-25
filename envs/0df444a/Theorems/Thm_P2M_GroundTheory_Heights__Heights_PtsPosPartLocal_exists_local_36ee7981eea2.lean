-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_exists_local_36ee7981eea2
-- name    : P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_exists_local_36ee7981eea2
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:16:47.065374+00:00
-- url     : https://prove2.me/theorems/93f8cb9c-b531-4d0c-ad0b-f011d188dade
-- title:
--   P2 M Ground Theory Heights  Heights Pts Pos Part Local exists local 36ee7981eea2: P2 M Ground Theory Heights  Heights Pts Pos Part Local exists local 36ee7981eea2
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Pos Part Local exists local 36ee7981eea2 construction uses the P2 M Ground Theory Heights  Heights Pts Pos Part Local exists local 36ee7981eea2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsPosPartLocal.lean#L149-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsPosPartLocal.lean#L149-L159

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

theorem P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_exists_local_36ee7981eea2 {P : Ideal (MRing ι)} {w₀ : ((k : K) → ι k) → ℂ} (h : IsSimpleSheetPt P Ψ w₀) :
    ∃ (y₀ : Fin e → ℂ) (γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ) (U : Set (Fin e → ℂ))
      (N : Set ((Fin e → ℂ) × (((k : K) → ι k) → ℂ))),
      IsOpen U ∧ IsOpen N ∧ (y₀, w₀) ∈ N ∧ segre (γ y₀) = w₀ ∧
      (∀ y ∈ U, DifferentiableAt ℂ γ y ∧ γ y ∈ mcPts P ∧ Ψ (segre (γ y)) = Fin.cons 1 y) ∧
      ∀ q ∈ N, q.1 ∈ U ∧ (q.2 ∈ fibre P Ψ q.1 → q.2 = segre (γ q.1)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsPosPartLocal».«exists_local» := P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_exists_local_36ee7981eea2
