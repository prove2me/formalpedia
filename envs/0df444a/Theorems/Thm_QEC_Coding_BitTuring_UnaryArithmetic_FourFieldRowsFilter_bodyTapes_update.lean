-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_bodyTapes_update
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.bodyTapes_update
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:05:42.963467+00:00
-- url     : https://prove2.me/theorems/5e4863c1-9276-414b-94aa-19b4de56bb5b
-- title:
--   Four Field Rows Filter: body Tapes update
-- statement:
--   Actual row-controller instruction, tape simulation, field phase or exact counted transfer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFourFieldRowsFilter.lean#L81-L85
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFourFieldRowsFilter.lean#L81-L85

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring Turing StateTransition
variable (P:Machine)

theorem QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.bodyTapes_update (C:List Bool) (S:P.K→List Bool) (k:P.K) (w:List Bool):
 Function.update (bodyTapes P C S) (.inl k) w=bodyTapes P C (Function.update S k w):= by sorry
