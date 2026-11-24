-- Prove2me | Theorems.Thm_P2M_GlobalTheory_UnitLemma_PairClass_trace___35abbd75f5d9
-- name    : P2M_GlobalTheory_UnitLemma_PairClass_trace___35abbd75f5d9
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:38:18.631847+00:00
-- url     : https://prove2.me/theorems/04a22573-2284-40e1-8846-bc434b113f86
-- title:
--   P2 M Global Theory Unit Lemma Pair Class trace   35abbd75f5d9: P2 M Global Theory Unit Lemma Pair Class trace   35abbd75f5d9
-- statement:
--   The P2 M Global Theory Unit Lemma Pair Class trace   35abbd75f5d9 construction uses the P2 M Global Theory Unit Lemma Pair Class trace   35abbd75f5d9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAevalEqOfSeparable.lean#L63-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAevalEqOfSeparable.lean#L63-L98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ExistsNeZeroAevalEqZero
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_UniNilp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAevalEqOfSeparable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.PairClass

theorem P2M_GlobalTheory_UnitLemma_PairClass_trace___35abbd75f5d9 (K : UQ) (B : InvAlg K) (a : B.A) :
    Algebra.trace K.E B.A (B.σ a) = K.c (Algebra.trace K.E B.A a) := by sorry

alias «GlobalTheory».«UnitLemma».«PairClass».«trace_σ» := P2M_GlobalTheory_UnitLemma_PairClass_trace___35abbd75f5d9
