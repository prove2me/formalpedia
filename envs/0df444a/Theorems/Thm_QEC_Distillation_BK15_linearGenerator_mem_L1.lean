-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_linearGenerator_mem_L1
-- name    : QEC.Distillation.BK15.linearGenerator_mem_L1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T00:54:55.512868+00:00
-- url     : https://prove2.me/theorems/fb803bce-59a7-4bd7-8622-4d4570bdd479
-- title:
--   BK15: linear Generator mem L1
-- statement:
--   The BK15 construction uses the linear Generator mem L1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L402-L403
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L402-L403

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.linearGenerator_mem_L1 (j : Fin 4) : linearGenerator j ∈ L1.carrier := by sorry
