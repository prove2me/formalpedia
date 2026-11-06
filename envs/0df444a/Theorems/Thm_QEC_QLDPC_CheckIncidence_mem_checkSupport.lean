-- Prove2me | Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
-- name    : QEC.QLDPC.CheckIncidence.mem_checkSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:19:47.672272+00:00
-- url     : https://prove2.me/theorems/815a8c74-f756-47d9-87a3-b0e070e52e39
-- title:
--   Check Incidence: mem check Support
-- statement:
--   The Check Incidence construction uses the mem check Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/Core.lean#L181-L184
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/Core.lean#L181-L184

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QLDPC_Core
set_option autoImplicit false
open QEC
universe u v w x
open scoped Classical
open QEC.QLDPC
open QEC.QLDPC.CheckIncidence
variable {χ ι : Type*} [Fintype χ] [Fintype ι]

theorem QEC.QLDPC.CheckIncidence.mem_checkSupport (I : CheckIncidence χ ι) (c : χ) (q : ι) :
    q ∈ I.checkSupport c ↔ I.incident c q := by sorry
