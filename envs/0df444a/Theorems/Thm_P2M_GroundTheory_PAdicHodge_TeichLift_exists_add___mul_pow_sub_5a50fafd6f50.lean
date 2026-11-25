-- Prove2me | Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_exists_add___mul_pow_sub_5a50fafd6f50
-- name    : P2M_GroundTheory_PAdicHodge_TeichLift_exists_add___mul_pow_sub_5a50fafd6f50
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:54:36.050941+00:00
-- url     : https://prove2.me/theorems/d53a4117-f313-5d1e-a7cf-51946dc9a973
-- title:
--   P2 M Ground Theory PAdic Hodge Teich Lift exists add   mul pow sub 5a50fafd6f50: P2 M Ground Theory PAdic Hodge Teich Lift exists add   mul pow sub 5a50fafd6f50
-- statement:
--   The P2 M Ground Theory PAdic Hodge Teich Lift exists add   mul pow sub 5a50fafd6f50 construction uses the P2 M Ground Theory PAdic Hodge Teich Lift exists add   mul pow sub 5a50fafd6f50 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L522-L530
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L522-L530

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

theorem P2M_GroundTheory_PAdicHodge_TeichLift_exists_add___mul_pow_sub_5a50fafd6f50 (A z : Γ) (hA : A ∈ T.int) (hz : z ∈ T.int) (k : ℕ) :
    ∃ w ∈ T.int, (A + T.π * z) ^ p ^ k - A ^ p ^ k = T.π ^ (k + 1) * w := by sorry

alias «GroundTheory».«PAdicHodge».«TeichLift».«exists_add_π_mul_pow_sub» := P2M_GroundTheory_PAdicHodge_TeichLift_exists_add___mul_pow_sub_5a50fafd6f50
