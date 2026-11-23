-- Prove2me | Theorems.Thm_P2M_GlobalTheory_UnitLemma_TwistUnit_trace___mem_daaee126bed4
-- name    : P2M_GlobalTheory_UnitLemma_TwistUnit_trace___mem_daaee126bed4
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:32:11.634822+00:00
-- url     : https://prove2.me/theorems/66eb0b3c-422f-43e8-add4-162ab026062d
-- title:
--   P2 M Global Theory Unit Lemma Twist Unit trace   mem daaee126bed4: P2 M Global Theory Unit Lemma Twist Unit trace   mem daaee126bed4
-- statement:
--   The P2 M Global Theory Unit Lemma Twist Unit trace   mem daaee126bed4 construction uses the P2 M Global Theory Unit Lemma Twist Unit trace   mem daaee126bed4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MemAdjoinOfMulEqOne.lean#L110-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MemAdjoinOfMulEqOne.lean#L110-L113

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

theorem P2M_GlobalTheory_UnitLemma_TwistUnit_trace___mem_daaee126bed4 (B : InvAlg K) (a : B.A) :
    Algebra.trace K.E B.A (B.σ a) ∈ (algebraMap K.O K.E).range ↔
      Algebra.trace K.E B.A a ∈ (algebraMap K.O K.E).range := by sorry

alias «GlobalTheory».«UnitLemma».«TwistUnit».«trace_σ_mem» := P2M_GlobalTheory_UnitLemma_TwistUnit_trace___mem_daaee126bed4
