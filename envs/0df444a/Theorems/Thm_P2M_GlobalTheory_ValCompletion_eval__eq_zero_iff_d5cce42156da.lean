-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ValCompletion_eval__eq_zero_iff_d5cce42156da
-- name    : P2M_GlobalTheory_ValCompletion_eval__eq_zero_iff_d5cce42156da
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:10:57.132467+00:00
-- url     : https://prove2.me/theorems/daa0dd63-7621-4e00-b708-d040c1239c17
-- title:
--   P2 M Global Theory Val Completion eval  eq zero iff d5cce42156da: P2 M Global Theory Val Completion eval  eq zero iff d5cce42156da
-- statement:
--   The P2 M Global Theory Val Completion eval  eq zero iff d5cce42156da construction uses the P2 M Global Theory Val Completion eval  eq zero iff d5cce42156da property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdicCompletionValuationRingCompleteValuationDoma.lean#L9-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdicCompletionValuationRingCompleteValuationDoma.lean#L9-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdicCompletionValuationRingCompleteValuationDoma
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
open GlobalTheory GlobalTheory.ValCompletion
variable {R : Type} [CommRing R] {I : Ideal R} {a : R}

theorem P2M_GlobalTheory_ValCompletion_eval__eq_zero_iff_d5cce42156da (h : I = Ideal.span {a}) (n : ℕ) (y : AdicCompletion I R) :
    AdicCompletion.evalₐ I n y = 0 ↔ algebraMap R (AdicCompletion I R) a ^ n ∣ y := by sorry

alias «GlobalTheory».«ValCompletion».«evalₐ_eq_zero_iff» := P2M_GlobalTheory_ValCompletion_eval__eq_zero_iff_d5cce42156da
