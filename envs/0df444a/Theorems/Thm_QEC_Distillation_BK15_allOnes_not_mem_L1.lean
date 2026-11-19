-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_allOnes_not_mem_L1
-- name    : QEC.Distillation.BK15.allOnes_not_mem_L1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T00:53:55.044172+00:00
-- url     : https://prove2.me/theorems/6bcbeabe-ddf7-4f22-a13a-beb7bc4c77c5
-- title:
--   BK15: all Ones not mem L1
-- statement:
--   The BK15 construction uses the all Ones not mem L1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L293-L295
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L293-L295

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.allOnes_not_mem_L1 : allOnes ∉ L1.carrier := by sorry
