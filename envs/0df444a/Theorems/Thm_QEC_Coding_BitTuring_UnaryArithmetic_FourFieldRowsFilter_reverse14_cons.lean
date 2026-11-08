-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_reverse14_cons
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.reverse14_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:07:00.949076+00:00
-- url     : https://prove2.me/theorems/518c5e7d-3d9a-47dc-ae43-8ccc5e25009c
-- title:
--   Four Field Rows Filter: reverse14 cons
-- statement:
--   Actual row-controller instruction, tape simulation, field phase or exact counted transfer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFourFieldRowsFilter.lean#L235-L241
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFourFieldRowsFilter.lean#L235-L241

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring Turing StateTransition
variable (P:Machine)

theorem QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.reverse14_cons (hio:P.input≠P.output) (f:Bool) (h:Option Bool) (I O H C B:List Bool) (a:Bool):
 TM2.step (program P) (cfg P 14 f h I O H (a::C) B)=some (cfg P 14 f (some a) I (a::O) H C B):= by sorry
