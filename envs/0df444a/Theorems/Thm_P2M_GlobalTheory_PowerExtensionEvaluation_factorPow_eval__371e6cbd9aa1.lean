-- Prove2me | Theorems.Thm_P2M_GlobalTheory_PowerExtensionEvaluation_factorPow_eval__371e6cbd9aa1
-- name    : P2M_GlobalTheory_PowerExtensionEvaluation_factorPow_eval__371e6cbd9aa1
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:08:01.310286+00:00
-- url     : https://prove2.me/theorems/b1ff8348-e64b-4991-834b-e3dae8959281
-- title:
--   P2 M Global Theory Power Extension Evaluation factor Pow eval  371e6cbd9aa1: P2 M Global Theory Power Extension Evaluation factor Pow eval  371e6cbd9aa1
-- statement:
--   The P2 M Global Theory Power Extension Evaluation factor Pow eval  371e6cbd9aa1 construction uses the P2 M Global Theory Power Extension Evaluation factor Pow eval  371e6cbd9aa1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/PowLeComapMapPow.lean#L11-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/PowLeComapMapPow.lean#L11-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowLeComapMapPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.PowerExtensionEvaluation

theorem P2M_GlobalTheory_PowerExtensionEvaluation_factorPow_eval__371e6cbd9aa1 {A : Type u_1} [CommRing A] (I : Ideal A) {m n : ℕ} (hle : m ≤ n)
    (x : AdicCompletion I A) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I m x := by sorry

alias «GlobalTheory».«PowerExtensionEvaluation».«factorPow_evalₐ» := P2M_GlobalTheory_PowerExtensionEvaluation_factorPow_eval__371e6cbd9aa1
