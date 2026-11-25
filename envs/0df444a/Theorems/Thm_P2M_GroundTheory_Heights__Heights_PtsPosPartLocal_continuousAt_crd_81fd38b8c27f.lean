-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_continuousAt_crd_81fd38b8c27f
-- name    : P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_continuousAt_crd_81fd38b8c27f
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:16:13.223522+00:00
-- url     : https://prove2.me/theorems/2ac58733-7dcb-44a2-a4e6-ff9ed0ae424a
-- title:
--   P2 M Ground Theory Heights  Heights Pts Pos Part Local continuous At crd 81fd38b8c27f: P2 M Ground Theory Heights  Heights Pts Pos Part Local continuous At crd 81fd38b8c27f
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Pos Part Local continuous At crd 81fd38b8c27f construction uses the P2 M Ground Theory Heights  Heights Pts Pos Part Local continuous At crd 81fd38b8c27f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsPosPartLocal.lean#L64-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsPosPartLocal.lean#L64-L71

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

theorem P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_continuousAt_crd_81fd38b8c27f {w : ((k : K) → ι k) → ℂ} (hw : Ψ w 0 ≠ 0) : ContinuousAt (crd Ψ) w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsPosPartLocal».«continuousAt_crd» := P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_continuousAt_crd_81fd38b8c27f
