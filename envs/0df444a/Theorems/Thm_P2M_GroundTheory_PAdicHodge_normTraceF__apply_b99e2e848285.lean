-- Prove2me | Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
-- name    : P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:24:53.471812+00:00
-- url     : https://prove2.me/theorems/3aed499d-5979-4820-8fa4-0924c39458f5
-- title:
--   P2 M Ground Theory PAdic Hodge norm Trace F  apply b99e2e848285: P2 M Ground Theory PAdic Hodge norm Trace F  apply b99e2e848285
-- statement:
--   The P2 M Ground Theory PAdic Hodge norm Trace F  apply b99e2e848285 construction uses the P2 M Ground Theory PAdic Hodge norm Trace F  apply b99e2e848285 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTrace.lean#L71-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTrace.lean#L71-L71

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial Module IntermediateField
noncomputable section
variable (F : Type*) {Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
variable [CharZero F] [Algebra.IsIntegral F Ω]

theorem P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285 (y : Ω) : normTraceFₗ F y = normTraceF F y := by sorry

alias «GroundTheory».«PAdicHodge».«normTraceFₗ_apply» := P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285

attribute [defeq] P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
