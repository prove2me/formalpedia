-- Prove2me | Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_algebraMap___mem_Econ_e50aaa839a7f
-- name    : P2M_GroundTheory_PAdicHodge_TeichLift_algebraMap___mem_Econ_e50aaa839a7f
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:30:44.415839+00:00
-- url     : https://prove2.me/theorems/9b8456f0-e38a-42e0-9d40-f549cf02987e
-- title:
--   P2 M Ground Theory PAdic Hodge Teich Lift algebra Map   mem Econ e50aaa839a7f: P2 M Ground Theory PAdic Hodge Teich Lift algebra Map   mem Econ e50aaa839a7f
-- statement:
--   The P2 M Ground Theory PAdic Hodge Teich Lift algebra Map   mem Econ e50aaa839a7f construction uses the P2 M Ground Theory PAdic Hodge Teich Lift algebra Map   mem Econ e50aaa839a7f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaBounded.lean#L692-L693
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaBounded.lean#L692-L693

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaBounded
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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.PAdicHodge
open Laurent Filter Topology
open GroundTheory.PAdicHodge.TeichLift
variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ) {ρ : ℝ}
variable {b c : T.B}

theorem P2M_GroundTheory_PAdicHodge_TeichLift_algebraMap___mem_Econ_e50aaa839a7f (ρ : Set.Ioo (0 : ℝ) 1) : algebraMap Γ T.B T.π ∈ T.Econ ρ := by sorry

alias «GroundTheory».«PAdicHodge».«TeichLift».«algebraMap_π_mem_Econ» := P2M_GroundTheory_PAdicHodge_TeichLift_algebraMap___mem_Econ_e50aaa839a7f
