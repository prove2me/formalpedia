-- Prove2me | Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift___mul_cancel_eaec830aa15d
-- name    : P2M_GroundTheory_PAdicHodge_TeichLift___mul_cancel_eaec830aa15d
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:09.855124+00:00
-- url     : https://prove2.me/theorems/88af43a1-d8da-4f09-a882-a6f6b366459c
-- title:
--   P2 M Ground Theory PAdic Hodge Teich Lift   mul cancel eaec830aa15d: P2 M Ground Theory PAdic Hodge Teich Lift   mul cancel eaec830aa15d
-- statement:
--   The P2 M Ground Theory PAdic Hodge Teich Lift   mul cancel eaec830aa15d construction uses the P2 M Ground Theory PAdic Hodge Teich Lift   mul cancel eaec830aa15d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L53-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L53-L54

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

theorem P2M_GroundTheory_PAdicHodge_TeichLift___mul_cancel_eaec830aa15d {x y : Γ} (h : T.π * x = T.π * y) : x = y := by sorry

alias «GroundTheory».«PAdicHodge».«TeichLift».«π_mul_cancel» := P2M_GroundTheory_PAdicHodge_TeichLift___mul_cancel_eaec830aa15d
