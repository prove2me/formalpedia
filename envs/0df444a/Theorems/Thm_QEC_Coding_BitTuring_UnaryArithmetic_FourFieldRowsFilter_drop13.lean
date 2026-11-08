-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_drop13
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.drop13
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:07:00.916345+00:00
-- url     : https://prove2.me/theorems/fb8aa4be-75c3-4691-b4f8-5973bef0541f
-- title:
--   Four Field Rows Filter: drop13
-- statement:
--   Actual row-controller instruction, tape simulation, field phase or exact counted transfer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFourFieldRowsFilter.lean#L226-L232
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFourFieldRowsFilter.lean#L226-L232

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring Turing StateTransition
variable (P:Machine)

theorem QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.drop13 (hio:P.input≠P.output) (f:Bool) (h:Option Bool) (I O H C B:List Bool) :
 TM2.step (program P) (cfg P 13 f h I O H C B)=some (cfg P 14 f C.head? I O H C.tail B):= by sorry
