-- Prove2me | Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_prefixLe___pow_mul_teich_fc75b8d33f82
-- name    : P2M_GroundTheory_PAdicHodge_TeichLift_prefixLe___pow_mul_teich_fc75b8d33f82
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:54:50.788528+00:00
-- url     : https://prove2.me/theorems/19f1482c-428d-4582-b3ca-b742eb53fa2e
-- title:
--   P2 M Ground Theory PAdic Hodge Teich Lift prefix Le   pow mul teich fc75b8d33f82: P2 M Ground Theory PAdic Hodge Teich Lift prefix Le   pow mul teich fc75b8d33f82
-- statement:
--   The P2 M Ground Theory PAdic Hodge Teich Lift prefix Le   pow mul teich fc75b8d33f82 construction uses the P2 M Ground Theory PAdic Hodge Teich Lift prefix Le   pow mul teich fc75b8d33f82 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L473-L479
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L473-L479

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

theorem P2M_GroundTheory_PAdicHodge_TeichLift_prefixLe___pow_mul_teich_fc75b8d33f82 (k : ℕ) (c : L) (n : ℕ) {b : ℝ} (hb : 0 ≤ b)
    (h : k ≤ n → ‖c‖ ≤ b) : T.PrefixLe (T.π ^ k * T.teich c) n b := by sorry

alias «GroundTheory».«PAdicHodge».«TeichLift».«prefixLe_π_pow_mul_teich» := P2M_GroundTheory_PAdicHodge_TeichLift_prefixLe___pow_mul_teich_fc75b8d33f82
