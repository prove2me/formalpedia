-- Prove2me | Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_red___ee117558e102
-- name    : P2M_GroundTheory_PAdicHodge_TeichLift_red___ee117558e102
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:12.769681+00:00
-- url     : https://prove2.me/theorems/17cc3bf4-c4a4-49b0-a614-7f531898cf4f
-- title:
--   P2 M Ground Theory PAdic Hodge Teich Lift red   ee117558e102: P2 M Ground Theory PAdic Hodge Teich Lift red   ee117558e102
-- statement:
--   The P2 M Ground Theory PAdic Hodge Teich Lift red   ee117558e102 construction uses the P2 M Ground Theory PAdic Hodge Teich Lift red   ee117558e102 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L46-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L46-L46

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
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
set_option linter.style.haveILetI false
open GroundTheory GroundTheory.PAdicHodge
open Ideal
open GroundTheory.PAdicHodge.TeichLift
variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CharP L p]
  [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

theorem P2M_GroundTheory_PAdicHodge_TeichLift_red___ee117558e102 : T.red T.π = 0 := by sorry

alias «GroundTheory».«PAdicHodge».«TeichLift».«red_π» := P2M_GroundTheory_PAdicHodge_TeichLift_red___ee117558e102
