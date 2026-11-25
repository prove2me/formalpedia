-- Prove2me | Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift___pow_mul_cancel_0b74b6c14644
-- name    : P2M_GroundTheory_PAdicHodge_TeichLift___pow_mul_cancel_0b74b6c14644
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:54:44.385551+00:00
-- url     : https://prove2.me/theorems/c427b530-d9b0-4b76-a733-e6f36f8287a1
-- title:
--   P2 M Ground Theory PAdic Hodge Teich Lift   pow mul cancel 0b74b6c14644: P2 M Ground Theory PAdic Hodge Teich Lift   pow mul cancel 0b74b6c14644
-- statement:
--   The P2 M Ground Theory PAdic Hodge Teich Lift   pow mul cancel 0b74b6c14644 construction uses the P2 M Ground Theory PAdic Hodge Teich Lift   pow mul cancel 0b74b6c14644 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L48-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L48-L51

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

theorem P2M_GroundTheory_PAdicHodge_TeichLift___pow_mul_cancel_0b74b6c14644 {n : ℕ} {x y : Γ} (h : T.π ^ n * x = T.π ^ n * y) : x = y := by sorry

alias «GroundTheory».«PAdicHodge».«TeichLift».«π_pow_mul_cancel» := P2M_GroundTheory_PAdicHodge_TeichLift___pow_mul_cancel_0b74b6c14644
