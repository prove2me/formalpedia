-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ValCompletion_factorPow_eval__29f3d9d0163b
-- name    : P2M_GlobalTheory_ValCompletion_factorPow_eval__29f3d9d0163b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:08.317307+00:00
-- url     : https://prove2.me/theorems/8d797bb7-2893-4f6d-8a93-ccd892c6b501
-- title:
--   P2 M Global Theory Val Completion factor Pow eval  29f3d9d0163b: P2 M Global Theory Val Completion factor Pow eval  29f3d9d0163b
-- statement:
--   The P2 M Global Theory Val Completion factor Pow eval  29f3d9d0163b construction uses the P2 M Global Theory Val Completion factor Pow eval  29f3d9d0163b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdicCompletionValuationRingCompleteValuationDoma.lean#L25-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdicCompletionValuationRingCompleteValuationDoma.lean#L25-L31

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

theorem P2M_GlobalTheory_ValCompletion_factorPow_eval__29f3d9d0163b {m n : ℕ} (h : m ≤ n) (y : AdicCompletion I R) :
    Ideal.Quotient.factorPow I h (AdicCompletion.evalₐ I n y) = AdicCompletion.evalₐ I m y := by sorry

alias «GlobalTheory».«ValCompletion».«factorPow_evalₐ» := P2M_GlobalTheory_ValCompletion_factorPow_eval__29f3d9d0163b
