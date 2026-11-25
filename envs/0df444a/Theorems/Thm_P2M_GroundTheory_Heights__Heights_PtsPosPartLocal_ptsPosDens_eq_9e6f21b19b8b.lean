-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_ptsPosDens_eq_9e6f21b19b8b
-- name    : P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_ptsPosDens_eq_9e6f21b19b8b
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:16:48.930885+00:00
-- url     : https://prove2.me/theorems/2a72739b-37a7-4968-805e-60f66bcddb6b
-- title:
--   P2 M Ground Theory Heights  Heights Pts Pos Part Local pts Pos Dens eq 9e6f21b19b8b: P2 M Ground Theory Heights  Heights Pts Pos Part Local pts Pos Dens eq 9e6f21b19b8b
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Pos Part Local pts Pos Dens eq 9e6f21b19b8b construction uses the P2 M Ground Theory Heights  Heights Pts Pos Part Local pts Pos Dens eq 9e6f21b19b8b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsPosPartLocal.lean#L206-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsPosPartLocal.lean#L206-L273

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

theorem P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_ptsPosDens_eq_9e6f21b19b8b {P : Ideal (MRing ι)} {L : Fin e → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    {g : ((Σ k, ι k) → ℂ) → ℝ}
    (hg : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → g (fun p => c p.1 * z p) = g z)
    {E : Set ((Σ k, ι k) → ℂ)}
    (hE : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → ((fun p => c p.1 * z p) ∈ E ↔ z ∈ E))
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {U : Set (Fin e → ℂ)}
    {N : Set ((Fin e → ℂ) × (((k : K) → ι k) → ℂ))} (hU : IsOpen U)
    (hγ : ∀ y ∈ U, DifferentiableAt ℂ γ y ∧ γ y ∈ mcPts P ∧ Ψ (segre (γ y)) = Fin.cons 1 y)
    (hN : IsOpen N) (hNp : ∀ q ∈ N, q.1 ∈ U ∧ (q.2 ∈ fibre P Ψ q.1 → q.2 = segre (γ q.1)))
    (hEN : ∀ z' ∈ E, Ψ (segre z') 0 ≠ 0 → (crd Ψ (segre z'), nrm Ψ (segre z')) ∈ N)
    (y : Fin e → ℂ) :
    ptsPosDens P Ψ (pot L) (E.indicator g) y = (U ∩ γ ⁻¹' E).indicator
      (fun y => max (g (γ y) * maDensity (fun j y' => pot L j (γ y')) y) 0) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsPosPartLocal».«ptsPosDens_eq» := P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_ptsPosDens_eq_9e6f21b19b8b
