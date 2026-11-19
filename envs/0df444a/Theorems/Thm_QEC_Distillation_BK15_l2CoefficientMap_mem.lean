-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_l2CoefficientMap_mem
-- name    : QEC.Distillation.BK15.l2CoefficientMap_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T00:52:45.218546+00:00
-- url     : https://prove2.me/theorems/ec2f9208-fc83-4946-84bf-9c17d5062a91
-- title:
--   BK15: l2 Coefficient Map mem
-- statement:
--   Every coefficient image used to enumerate `L2` is a genuine `L2` codeword.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L193-L195
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L193-L195

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.l2CoefficientMap_mem (a : Sum (Fin 4) QuadraticIndex → Bit) :
    l2CoefficientMap a ∈ L2.carrier := by sorry
