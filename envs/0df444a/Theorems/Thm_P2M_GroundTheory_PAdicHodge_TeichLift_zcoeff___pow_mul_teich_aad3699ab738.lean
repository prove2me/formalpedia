-- Prove2me | Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_zcoeff___pow_mul_teich_aad3699ab738
-- name    : P2M_GroundTheory_PAdicHodge_TeichLift_zcoeff___pow_mul_teich_aad3699ab738
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:26:21.555374+00:00
-- url     : https://prove2.me/theorems/298922dd-7b37-59c8-bd4f-55528fd3b542
-- title:
--   P2 M Ground Theory PAdic Hodge Teich Lift zcoeff   pow mul teich aad3699ab738: P2 M Ground Theory PAdic Hodge Teich Lift zcoeff   pow mul teich aad3699ab738
-- statement:
--   The P2 M Ground Theory PAdic Hodge Teich Lift zcoeff   pow mul teich aad3699ab738 construction uses the P2 M Ground Theory PAdic Hodge Teich Lift zcoeff   pow mul teich aad3699ab738 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaBounded.lean#L559-L565
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaBounded.lean#L559-L565

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

theorem P2M_GroundTheory_PAdicHodge_TeichLift_zcoeff___pow_mul_teich_aad3699ab738 (N : ℕ) (c : L) : T.zcoeff (T.π ^ N * T.teich c) = Pi.single (N : ℤ) c := by sorry

alias «GroundTheory».«PAdicHodge».«TeichLift».«zcoeff_π_pow_mul_teich» := P2M_GroundTheory_PAdicHodge_TeichLift_zcoeff___pow_mul_teich_aad3699ab738
