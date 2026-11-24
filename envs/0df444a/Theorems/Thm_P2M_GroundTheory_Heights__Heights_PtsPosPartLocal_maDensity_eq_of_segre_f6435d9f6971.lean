-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_maDensity_eq_of_segre_f6435d9f6971
-- name    : P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_maDensity_eq_of_segre_f6435d9f6971
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:27.599537+00:00
-- url     : https://prove2.me/theorems/98868a08-866c-4f03-876d-7918c2b5bbf3
-- title:
--   P2 M Ground Theory Heights  Heights Pts Pos Part Local ma Density eq of segre f6435d9f6971: P2 M Ground Theory Heights  Heights Pts Pos Part Local ma Density eq of segre f6435d9f6971
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Pos Part Local ma Density eq of segre f6435d9f6971 construction uses the P2 M Ground Theory Heights  Heights Pts Pos Part Local ma Density eq of segre f6435d9f6971 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsPosPartLocal.lean#L134-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsPosPartLocal.lean#L134-L147

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

theorem P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_maDensity_eq_of_segre_f6435d9f6971 {L : Fin e → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    {γ γ' : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {y : Fin e → ℂ} (hγ : AnalyticAt ℂ γ y)
    (hγ' : AnalyticAt ℂ γ' y) (hy : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0)
    (hseg : (fun y' => segre (γ y')) =ᶠ[𝓝 y] fun y' => segre (γ' y')) :
    maDensity (fun j y' => pot L j (γ' y')) y = maDensity (fun j y' => pot L j (γ y')) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsPosPartLocal».«maDensity_eq_of_segre» := P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_maDensity_eq_of_segre_f6435d9f6971
