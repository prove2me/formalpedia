-- Prove2me | Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_eq_teich_add___mul_tail_16271f5c650a
-- name    : P2M_GroundTheory_PAdicHodge_TeichLift_eq_teich_add___mul_tail_16271f5c650a
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:54:42.500329+00:00
-- url     : https://prove2.me/theorems/014e2a78-7f7d-4e0b-b1de-ab52756db115
-- title:
--   P2 M Ground Theory PAdic Hodge Teich Lift eq teich add   mul tail 16271f5c650a: P2 M Ground Theory PAdic Hodge Teich Lift eq teich add   mul tail 16271f5c650a
-- statement:
--   The P2 M Ground Theory PAdic Hodge Teich Lift eq teich add   mul tail 16271f5c650a construction uses the P2 M Ground Theory PAdic Hodge Teich Lift eq teich add   mul tail 16271f5c650a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L129-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L129-L130

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

theorem P2M_GroundTheory_PAdicHodge_TeichLift_eq_teich_add___mul_tail_16271f5c650a (x : Γ) : x = T.teich (T.red x) + T.π * T.tail x := by sorry

alias «GroundTheory».«PAdicHodge».«TeichLift».«eq_teich_add_π_mul_tail» := P2M_GroundTheory_PAdicHodge_TeichLift_eq_teich_add___mul_tail_16271f5c650a
