-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_sheetDensity_eq_f776bfe0d7d4
-- name    : P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_sheetDensity_eq_f776bfe0d7d4
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:16:50.265652+00:00
-- url     : https://prove2.me/theorems/73e8b78e-a2e6-4ca8-a2a8-91566d0d3475
-- title:
--   P2 M Ground Theory Heights  Heights Pts Pos Part Local sheet Density eq f776bfe0d7d4: P2 M Ground Theory Heights  Heights Pts Pos Part Local sheet Density eq f776bfe0d7d4
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Pos Part Local sheet Density eq f776bfe0d7d4 construction uses the P2 M Ground Theory Heights  Heights Pts Pos Part Local sheet Density eq f776bfe0d7d4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsPosPartLocal.lean#L177-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsPosPartLocal.lean#L177-L204

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

theorem P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_sheetDensity_eq_f776bfe0d7d4 {P : Ideal (MRing ι)} {L : Fin e → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    {G : ((Σ k, ι k) → ℂ) → ℝ}
    (hG : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → G (fun p => c p.1 * z p) = G z)
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {U : Set (Fin e → ℂ)}
    {N : Set ((Fin e → ℂ) × (((k : K) → ι k) → ℂ))} (hU : IsOpen U)
    (hγ : ∀ y ∈ U, DifferentiableAt ℂ γ y ∧ γ y ∈ mcPts P ∧ Ψ (segre (γ y)) = Fin.cons 1 y)
    (hN : IsOpen N) (hNp : ∀ q ∈ N, q.1 ∈ U ∧ (q.2 ∈ fibre P Ψ q.1 → q.2 = segre (γ q.1)))
    {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} (hq : (y, w) ∈ N) (hw : w ∈ fibre P Ψ y) :
    sheetDensity P Ψ (pot L) G y w = G (γ y) * maDensity (fun j y' => pot L j (γ y')) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsPosPartLocal».«sheetDensity_eq» := P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_sheetDensity_eq_f776bfe0d7d4
