-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_nrm_smul_70d405fd40ea
-- name    : P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_nrm_smul_70d405fd40ea
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:46.651439+00:00
-- url     : https://prove2.me/theorems/7d2c09c3-3edc-461a-a3ab-a7d5b40549f1
-- title:
--   P2 M Ground Theory Heights  Heights Pts Pos Part Local nrm smul 70d405fd40ea: P2 M Ground Theory Heights  Heights Pts Pos Part Local nrm smul 70d405fd40ea
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Pos Part Local nrm smul 70d405fd40ea construction uses the P2 M Ground Theory Heights  Heights Pts Pos Part Local nrm smul 70d405fd40ea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsPosPartLocal.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsPosPartLocal.lean#L37-L39

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

theorem P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_nrm_smul_70d405fd40ea {t : ℂ} (ht : t ≠ 0) (w : ((k : K) → ι k) → ℂ) : nrm Ψ (t • w) = nrm Ψ w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsPosPartLocal».«nrm_smul» := P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_nrm_smul_70d405fd40ea
