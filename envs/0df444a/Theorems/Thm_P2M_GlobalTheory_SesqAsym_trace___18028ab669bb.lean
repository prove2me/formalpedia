-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SesqAsym_trace___18028ab669bb
-- name    : P2M_GlobalTheory_SesqAsym_trace___18028ab669bb
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:38:36.56282+00:00
-- url     : https://prove2.me/theorems/abd6fdd3-f6d1-44db-8f0e-94a18c52eb36
-- title:
--   P2 M Global Theory Sesq Asym trace   18028ab669bb: P2 M Global Theory Sesq Asym trace   18028ab669bb
-- statement:
--   The P2 M Global Theory Sesq Asym trace   18028ab669bb construction uses the P2 M Global Theory Sesq Asym trace   18028ab669bb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SesqAsym.lean#L10-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SesqAsym.lean#L10-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAevalEqOfCharpolySeparableInvolutionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfTraceMulOfSeparableGeneratedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitSigmaEqMulHilbert90InvAlgStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SesqAsym
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.SesqAsym

theorem P2M_GlobalTheory_SesqAsym_trace___18028ab669bb {K : UQ} (B : InvAlg K) (a : B.A) :
    Algebra.trace K.E B.A (B.σ a) = K.c (Algebra.trace K.E B.A a) := by sorry

alias «GlobalTheory».«SesqAsym».«trace_σ» := P2M_GlobalTheory_SesqAsym_trace___18028ab669bb
