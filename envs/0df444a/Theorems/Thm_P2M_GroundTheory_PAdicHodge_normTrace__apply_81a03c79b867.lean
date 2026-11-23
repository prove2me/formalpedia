-- Prove2me | Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867
-- name    : P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:24:28.661306+00:00
-- url     : https://prove2.me/theorems/ad46ae52-d0d5-40eb-967a-386cc19f47ff
-- title:
--   P2 M Ground Theory PAdic Hodge norm Trace  apply 81a03c79b867: P2 M Ground Theory PAdic Hodge norm Trace  apply 81a03c79b867
-- statement:
--   The P2 M Ground Theory PAdic Hodge norm Trace  apply 81a03c79b867 construction uses the P2 M Ground Theory PAdic Hodge norm Trace  apply 81a03c79b867 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTrace.lean#L73-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTrace.lean#L73-L73

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

theorem P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867 (y : Ω) : normTraceₗ F y = normTrace F y := by sorry

alias «GroundTheory».«PAdicHodge».«normTraceₗ_apply» := P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867

attribute [defeq] P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867
