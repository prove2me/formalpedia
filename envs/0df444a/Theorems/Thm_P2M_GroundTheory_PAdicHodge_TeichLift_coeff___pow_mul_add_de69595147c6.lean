-- Prove2me | Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_coeff___pow_mul_add_de69595147c6
-- name    : P2M_GroundTheory_PAdicHodge_TeichLift_coeff___pow_mul_add_de69595147c6
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:56.603903+00:00
-- url     : https://prove2.me/theorems/e736b4cc-9da5-4909-9837-2e64120f9f5c
-- title:
--   P2 M Ground Theory PAdic Hodge Teich Lift coeff   pow mul add de69595147c6: P2 M Ground Theory PAdic Hodge Teich Lift coeff   pow mul add de69595147c6
-- statement:
--   The P2 M Ground Theory PAdic Hodge Teich Lift coeff   pow mul add de69595147c6 construction uses the P2 M Ground Theory PAdic Hodge Teich Lift coeff   pow mul add de69595147c6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L273-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L273-L277

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

theorem P2M_GroundTheory_PAdicHodge_TeichLift_coeff___pow_mul_add_de69595147c6 (k : ℕ) (x : Γ) (n : ℕ) :
    T.coeff (T.π ^ k * x) (n + k) = T.coeff x n := by sorry

alias «GroundTheory».«PAdicHodge».«TeichLift».«coeff_π_pow_mul_add» := P2M_GroundTheory_PAdicHodge_TeichLift_coeff___pow_mul_add_de69595147c6
