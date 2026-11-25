-- Prove2me | Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_mem_span_pow_of___mul_3e1ac1a2d1bc
-- name    : P2M_GroundTheory_PAdicHodge_TeichLift_mem_span_pow_of___mul_3e1ac1a2d1bc
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:54:54.129801+00:00
-- url     : https://prove2.me/theorems/4619474e-a621-496e-8a49-0eeb2bea2b0e
-- title:
--   P2 M Ground Theory PAdic Hodge Teich Lift mem span pow of   mul 3e1ac1a2d1bc: P2 M Ground Theory PAdic Hodge Teich Lift mem span pow of   mul 3e1ac1a2d1bc
-- statement:
--   The P2 M Ground Theory PAdic Hodge Teich Lift mem span pow of   mul 3e1ac1a2d1bc construction uses the P2 M Ground Theory PAdic Hodge Teich Lift mem span pow of   mul 3e1ac1a2d1bc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L56-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L56-L60

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

theorem P2M_GroundTheory_PAdicHodge_TeichLift_mem_span_pow_of___mul_3e1ac1a2d1bc {n : ℕ} {x : Γ} (h : T.π * x ∈ Ideal.span {T.π ^ (n + 1)}) :
    x ∈ Ideal.span {T.π ^ n} := by sorry

alias «GroundTheory».«PAdicHodge».«TeichLift».«mem_span_pow_of_π_mul» := P2M_GroundTheory_PAdicHodge_TeichLift_mem_span_pow_of___mul_3e1ac1a2d1bc
