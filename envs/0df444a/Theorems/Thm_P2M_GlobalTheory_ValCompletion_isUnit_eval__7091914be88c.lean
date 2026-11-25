-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ValCompletion_isUnit_eval__7091914be88c
-- name    : P2M_GlobalTheory_ValCompletion_isUnit_eval__7091914be88c
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:10:46.113925+00:00
-- url     : https://prove2.me/theorems/82c55df3-2390-461f-9dd9-8dcc72431b18
-- title:
--   P2 M Global Theory Val Completion is Unit eval  7091914be88c: P2 M Global Theory Val Completion is Unit eval  7091914be88c
-- statement:
--   The P2 M Global Theory Val Completion is Unit eval  7091914be88c construction uses the P2 M Global Theory Val Completion is Unit eval  7091914be88c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdicCompletionValuationRingCompleteValuationDoma.lean#L33-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdicCompletionValuationRingCompleteValuationDoma.lean#L33-L51

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

theorem P2M_GlobalTheory_ValCompletion_isUnit_eval__7091914be88c (y : AdicCompletion I R) (hy : IsUnit (AdicCompletion.evalₐ I 1 y)) (n : ℕ) :
    IsUnit (AdicCompletion.evalₐ I n y) := by sorry

alias «GlobalTheory».«ValCompletion».«isUnit_evalₐ» := P2M_GlobalTheory_ValCompletion_isUnit_eval__7091914be88c
