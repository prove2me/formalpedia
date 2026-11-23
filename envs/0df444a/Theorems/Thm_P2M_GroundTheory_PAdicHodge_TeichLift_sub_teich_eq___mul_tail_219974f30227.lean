-- Prove2me | Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_sub_teich_eq___mul_tail_219974f30227
-- name    : P2M_GroundTheory_PAdicHodge_TeichLift_sub_teich_eq___mul_tail_219974f30227
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:07.875652+00:00
-- url     : https://prove2.me/theorems/96dbe7a6-6967-4688-bca6-74b07695da2f
-- title:
--   P2 M Ground Theory PAdic Hodge Teich Lift sub teich eq   mul tail 219974f30227: P2 M Ground Theory PAdic Hodge Teich Lift sub teich eq   mul tail 219974f30227
-- statement:
--   The P2 M Ground Theory PAdic Hodge Teich Lift sub teich eq   mul tail 219974f30227 construction uses the P2 M Ground Theory PAdic Hodge Teich Lift sub teich eq   mul tail 219974f30227 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L126-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L126-L127

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

theorem P2M_GroundTheory_PAdicHodge_TeichLift_sub_teich_eq___mul_tail_219974f30227 (x : Γ) : x - T.teich (T.red x) = T.π * T.tail x := by sorry

alias «GroundTheory».«PAdicHodge».«TeichLift».«sub_teich_eq_π_mul_tail» := P2M_GroundTheory_PAdicHodge_TeichLift_sub_teich_eq___mul_tail_219974f30227
