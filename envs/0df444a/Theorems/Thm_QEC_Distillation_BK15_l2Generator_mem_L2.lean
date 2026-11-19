-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_l2Generator_mem_L2
-- name    : QEC.Distillation.BK15.l2Generator_mem_L2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T00:54:58.517797+00:00
-- url     : https://prove2.me/theorems/81efbb1f-d132-4bd7-9db7-40cb759786d6
-- title:
--   BK15: l2 Generator mem L2
-- statement:
--   The BK15 construction uses the l2 Generator mem L2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L405-L407
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L405-L407

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.l2Generator_mem_L2 (g : Sum (Fin 4) QuadraticIndex) :
    l2Generator g ∈ L2.carrier := by sorry
