-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_stepAuxBody
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.stepAuxBody
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:05:58.216209+00:00
-- url     : https://prove2.me/theorems/696b39f4-6a0a-4668-9ef0-e4f03adf8584
-- title:
--   Four Field Rows Filter: step Aux Body
-- statement:
--   Actual row-controller instruction, tape simulation, field phase or exact counted transfer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFourFieldRowsFilter.lean#L87-L93
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFourFieldRowsFilter.lean#L87-L93

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring Turing StateTransition
variable (P:Machine)

theorem QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.stepAuxBody (C:List Bool) (l:P.Λ) (v:P.σ) (S:P.K→List Bool):
 TM2.stepAux (program P (.inl l)) (v,false,none) (bodyTapes P C S)=
 embedBody P C (TM2.stepAux (P.program l) v S):= by sorry
