-- Prove2me | Theorems.Thm_P2M_GlobalTheory_UnitLemma_TwistUnit_trace___3993ddab228e
-- name    : P2M_GlobalTheory_UnitLemma_TwistUnit_trace___3993ddab228e
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:11:30.59549+00:00
-- url     : https://prove2.me/theorems/28997ee4-0963-4ba5-981f-6437961dae69
-- title:
--   P2 M Global Theory Unit Lemma Twist Unit trace   3993ddab228e: P2 M Global Theory Unit Lemma Twist Unit trace   3993ddab228e
-- statement:
--   The P2 M Global Theory Unit Lemma Twist Unit trace   3993ddab228e construction uses the P2 M Global Theory Unit Lemma Twist Unit trace   3993ddab228e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MemAdjoinOfMulEqOne.lean#L58-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MemAdjoinOfMulEqOne.lean#L58-L98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitBasePointAdjoinTwistedSigmaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemAdjoinOfMulEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.TwistUnit
open GlobalTheory.UnitLemma Polynomial
variable {K : UQ}

theorem P2M_GlobalTheory_UnitLemma_TwistUnit_trace___3993ddab228e (B : InvAlg K) (a : B.A) :
    Algebra.trace K.E B.A (B.σ a) = K.c (Algebra.trace K.E B.A a) := by sorry

alias «GlobalTheory».«UnitLemma».«TwistUnit».«trace_σ» := P2M_GlobalTheory_UnitLemma_TwistUnit_trace___3993ddab228e
