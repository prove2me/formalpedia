-- Prove2me | Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_coeff___pow_mul_teich_43d14c6acc24
-- name    : P2M_GroundTheory_PAdicHodge_TeichLift_coeff___pow_mul_teich_43d14c6acc24
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:04.565586+00:00
-- url     : https://prove2.me/theorems/6393d997-e9e4-40fd-bc5e-5ed9ad62179f
-- title:
--   P2 M Ground Theory PAdic Hodge Teich Lift coeff   pow mul teich 43d14c6acc24: P2 M Ground Theory PAdic Hodge Teich Lift coeff   pow mul teich 43d14c6acc24
-- statement:
--   The P2 M Ground Theory PAdic Hodge Teich Lift coeff   pow mul teich 43d14c6acc24 construction uses the P2 M Ground Theory PAdic Hodge Teich Lift coeff   pow mul teich 43d14c6acc24 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L319-L325
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L319-L325

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

theorem P2M_GroundTheory_PAdicHodge_TeichLift_coeff___pow_mul_teich_43d14c6acc24 (k : ℕ) (c : L) (n : ℕ) :
    T.coeff (T.π ^ k * T.teich c) n = if n = k then c else 0 := by sorry

alias «GroundTheory».«PAdicHodge».«TeichLift».«coeff_π_pow_mul_teich» := P2M_GroundTheory_PAdicHodge_TeichLift_coeff___pow_mul_teich_43d14c6acc24
