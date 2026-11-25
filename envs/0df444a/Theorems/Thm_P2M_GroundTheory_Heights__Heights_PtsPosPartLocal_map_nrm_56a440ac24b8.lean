-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_map_nrm_56a440ac24b8
-- name    : P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_map_nrm_56a440ac24b8
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:16:21.129936+00:00
-- url     : https://prove2.me/theorems/f185cd76-8108-4b43-bfe5-6abd6020de74
-- title:
--   P2 M Ground Theory Heights  Heights Pts Pos Part Local map nrm 56a440ac24b8: P2 M Ground Theory Heights  Heights Pts Pos Part Local map nrm 56a440ac24b8
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Pos Part Local map nrm 56a440ac24b8 construction uses the P2 M Ground Theory Heights  Heights Pts Pos Part Local map nrm 56a440ac24b8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsPosPartLocal.lean#L31-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsPosPartLocal.lean#L31-L35

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

theorem P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_map_nrm_56a440ac24b8 {w : ((k : K) → ι k) → ℂ} (hw : Ψ w 0 ≠ 0) : Ψ (nrm Ψ w) = Fin.cons 1 (crd Ψ w) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsPosPartLocal».«map_nrm» := P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_map_nrm_56a440ac24b8
