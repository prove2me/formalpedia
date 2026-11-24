-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_maDensity_bsmul_f913413ea179
-- name    : P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_maDensity_bsmul_f913413ea179
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:13.312096+00:00
-- url     : https://prove2.me/theorems/b401479e-041a-4719-9491-cfcdb94859df
-- title:
--   P2 M Ground Theory Heights  Heights Pts Pos Part Local ma Density bsmul f913413ea179: P2 M Ground Theory Heights  Heights Pts Pos Part Local ma Density bsmul f913413ea179
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Pos Part Local ma Density bsmul f913413ea179 construction uses the P2 M Ground Theory Heights  Heights Pts Pos Part Local ma Density bsmul f913413ea179 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsPosPartLocal.lean#L94-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsPosPartLocal.lean#L94-L132

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

theorem P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_maDensity_bsmul_f913413ea179 {L : Fin e → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    {γ γ' : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {c : K → (Fin e → ℂ) → ℂ} {y : Fin e → ℂ}
    (hγ : AnalyticAt ℂ γ y) (hy : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0) (hcan : ∀ k, AnalyticAt ℂ (c k) y)
    (hc0 : ∀ k, c k y ≠ 0) (hrel : ∀ᶠ y' in 𝓝 y, γ' y' = bsmul (fun k => c k y') (γ y')) :
    maDensity (fun j y' => pot L j (γ' y')) y = maDensity (fun j y' => pot L j (γ y')) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsPosPartLocal».«maDensity_bsmul» := P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_maDensity_bsmul_f913413ea179
