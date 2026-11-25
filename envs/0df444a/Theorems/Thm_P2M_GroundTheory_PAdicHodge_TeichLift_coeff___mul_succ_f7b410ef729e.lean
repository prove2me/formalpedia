-- Prove2me | Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_succ_f7b410ef729e
-- name    : P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_succ_f7b410ef729e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:46.495274+00:00
-- url     : https://prove2.me/theorems/1ae8d825-a4ab-4f50-92fa-fcc9156d4722
-- title:
--   P2 M Ground Theory PAdic Hodge Teich Lift coeff   mul succ f7b410ef729e: P2 M Ground Theory PAdic Hodge Teich Lift coeff   mul succ f7b410ef729e
-- statement:
--   The P2 M Ground Theory PAdic Hodge Teich Lift coeff   mul succ f7b410ef729e construction uses the P2 M Ground Theory PAdic Hodge Teich Lift coeff   mul succ f7b410ef729e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L267-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L267-L268

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

theorem P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_succ_f7b410ef729e (x : Γ) (n : ℕ) : T.coeff (T.π * x) (n + 1) = T.coeff x n := by sorry

alias «GroundTheory».«PAdicHodge».«TeichLift».«coeff_π_mul_succ» := P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_succ_f7b410ef729e
