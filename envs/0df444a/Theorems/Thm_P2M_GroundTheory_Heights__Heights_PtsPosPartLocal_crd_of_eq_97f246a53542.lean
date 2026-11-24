-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_crd_of_eq_97f246a53542
-- name    : P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_crd_of_eq_97f246a53542
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:14.879505+00:00
-- url     : https://prove2.me/theorems/c8ce90c7-3611-4f68-8bd2-e3ef7fba677d
-- title:
--   P2 M Ground Theory Heights  Heights Pts Pos Part Local crd of eq 97f246a53542: P2 M Ground Theory Heights  Heights Pts Pos Part Local crd of eq 97f246a53542
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Pos Part Local crd of eq 97f246a53542 construction uses the P2 M Ground Theory Heights  Heights Pts Pos Part Local crd of eq 97f246a53542 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsPosPartLocal.lean#L48-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsPosPartLocal.lean#L48-L50

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

theorem P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_crd_of_eq_97f246a53542 {w : ((k : K) → ι k) → ℂ} {y : Fin e → ℂ} (h : Ψ w = Fin.cons 1 y) : crd Ψ w = y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsPosPartLocal».«crd_of_eq» := P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_crd_of_eq_97f246a53542
