-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_continuousAt_nrm_d1e525da6af0
-- name    : P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_continuousAt_nrm_d1e525da6af0
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:21:32.551188+00:00
-- url     : https://prove2.me/theorems/088749ce-9b89-5127-8146-7fb64f2438ba
-- title:
--   P2 M Ground Theory Heights  Heights Pts Pos Part Local continuous At nrm d1e525da6af0: P2 M Ground Theory Heights  Heights Pts Pos Part Local continuous At nrm d1e525da6af0
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Pos Part Local continuous At nrm d1e525da6af0 construction uses the P2 M Ground Theory Heights  Heights Pts Pos Part Local continuous At nrm d1e525da6af0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsPosPartLocal.lean#L73-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsPosPartLocal.lean#L73-L75

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

theorem P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_continuousAt_nrm_d1e525da6af0 {w : ((k : K) → ι k) → ℂ} (hw : Ψ w 0 ≠ 0) : ContinuousAt (nrm Ψ) w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsPosPartLocal».«continuousAt_nrm» := P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_continuousAt_nrm_d1e525da6af0
