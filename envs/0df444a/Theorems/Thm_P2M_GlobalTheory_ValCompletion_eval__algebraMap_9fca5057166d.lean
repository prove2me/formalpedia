-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ValCompletion_eval__algebraMap_9fca5057166d
-- name    : P2M_GlobalTheory_ValCompletion_eval__algebraMap_9fca5057166d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:22.897802+00:00
-- url     : https://prove2.me/theorems/833d80e6-c9cb-43da-99e5-7b30513a150e
-- title:
--   P2 M Global Theory Val Completion eval  algebra Map 9fca5057166d: P2 M Global Theory Val Completion eval  algebra Map 9fca5057166d
-- statement:
--   The P2 M Global Theory Val Completion eval  algebra Map 9fca5057166d construction uses the P2 M Global Theory Val Completion eval  algebra Map 9fca5057166d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdicCompletionValuationRingCompleteValuationDoma.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdicCompletionValuationRingCompleteValuationDoma.lean#L21-L23

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

theorem P2M_GlobalTheory_ValCompletion_eval__algebraMap_9fca5057166d (n : ℕ) (r : R) :
    AdicCompletion.evalₐ I n (algebraMap R (AdicCompletion I R) r) = Ideal.Quotient.mk _ r := by sorry

alias «GlobalTheory».«ValCompletion».«evalₐ_algebraMap» := P2M_GlobalTheory_ValCompletion_eval__algebraMap_9fca5057166d
