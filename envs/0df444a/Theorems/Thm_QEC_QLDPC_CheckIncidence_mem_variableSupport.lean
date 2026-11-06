-- Prove2me | Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
-- name    : QEC.QLDPC.CheckIncidence.mem_variableSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:19:57.17099+00:00
-- url     : https://prove2.me/theorems/70b2fb47-ecb6-4d43-a8bf-acbb8a0db4b5
-- title:
--   Check Incidence: mem variable Support
-- statement:
--   The Check Incidence construction uses the mem variable Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/Core.lean#L187-L190
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/Core.lean#L187-L190

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QLDPC_Core
set_option autoImplicit false
open QEC
universe u v w x
open scoped Classical
open QEC.QLDPC
open QEC.QLDPC.CheckIncidence
variable {χ ι : Type*} [Fintype χ] [Fintype ι]

theorem QEC.QLDPC.CheckIncidence.mem_variableSupport (I : CheckIncidence χ ι) (c : χ) (q : ι) :
    c ∈ I.variableSupport q ↔ I.incident c q := by sorry
