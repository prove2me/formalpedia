-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_analyticOnNhd_of_diffOn_dfa8683cecfc
-- name    : P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_analyticOnNhd_of_diffOn_dfa8683cecfc
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:20.111109+00:00
-- url     : https://prove2.me/theorems/2c8de124-62ec-46d3-8dc2-fde0ed495569
-- title:
--   P2 M Ground Theory Heights  Heights Pts Pos Part Local analytic On Nhd of diff On dfa8683cecfc: P2 M Ground Theory Heights  Heights Pts Pos Part Local analytic On Nhd of diff On dfa8683cecfc
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Pos Part Local analytic On Nhd of diff On dfa8683cecfc construction uses the P2 M Ground Theory Heights  Heights Pts Pos Part Local analytic On Nhd of diff On dfa8683cecfc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsPosPartLocal.lean#L80-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsPosPartLocal.lean#L80-L84

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

theorem P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_analyticOnNhd_of_diffOn_dfa8683cecfc {m : ℕ} {σ : Type*} [Fintype σ] {U : Set (Fin m → ℂ)}
    {f : (Fin m → ℂ) → σ → ℂ} (hU : IsOpen U) (hf : ∀ y ∈ U, DifferentiableAt ℂ f y) :
    AnalyticOnNhd ℂ f U := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsPosPartLocal».«analyticOnNhd_of_diffOn» := P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_analyticOnNhd_of_diffOn_dfa8683cecfc
