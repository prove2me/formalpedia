-- Prove2me | Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_zero_c24e500c7aa0
-- name    : P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_zero_c24e500c7aa0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:00.854333+00:00
-- url     : https://prove2.me/theorems/8a9eaa6c-880c-430f-bcb5-2e1701714b5c
-- title:
--   P2 M Ground Theory PAdic Hodge Teich Lift coeff   mul zero c24e500c7aa0: P2 M Ground Theory PAdic Hodge Teich Lift coeff   mul zero c24e500c7aa0
-- statement:
--   The P2 M Ground Theory PAdic Hodge Teich Lift coeff   mul zero c24e500c7aa0 construction uses the P2 M Ground Theory PAdic Hodge Teich Lift coeff   mul zero c24e500c7aa0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L270-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L270-L271

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

theorem P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_zero_c24e500c7aa0 (x : Γ) : T.coeff (T.π * x) 0 = 0 := by sorry

alias «GroundTheory».«PAdicHodge».«TeichLift».«coeff_π_mul_zero» := P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_zero_c24e500c7aa0
