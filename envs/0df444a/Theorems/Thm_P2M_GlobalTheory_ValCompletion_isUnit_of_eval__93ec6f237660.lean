-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ValCompletion_isUnit_of_eval__93ec6f237660
-- name    : P2M_GlobalTheory_ValCompletion_isUnit_of_eval__93ec6f237660
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:11:56.219799+00:00
-- url     : https://prove2.me/theorems/0f19288d-bb7a-4efc-a863-af81e25dd301
-- title:
--   P2 M Global Theory Val Completion is Unit of eval  93ec6f237660: P2 M Global Theory Val Completion is Unit of eval  93ec6f237660
-- statement:
--   The P2 M Global Theory Val Completion is Unit of eval  93ec6f237660 construction uses the P2 M Global Theory Val Completion is Unit of eval  93ec6f237660 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdicCompletionValuationRingCompleteValuationDoma.lean#L53-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdicCompletionValuationRingCompleteValuationDoma.lean#L53-L66

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

theorem P2M_GlobalTheory_ValCompletion_isUnit_of_eval__93ec6f237660 (y : AdicCompletion I R) (hy : IsUnit (AdicCompletion.evalₐ I 1 y)) :
    IsUnit y := by sorry

alias «GlobalTheory».«ValCompletion».«isUnit_of_evalₐ» := P2M_GlobalTheory_ValCompletion_isUnit_of_eval__93ec6f237660
