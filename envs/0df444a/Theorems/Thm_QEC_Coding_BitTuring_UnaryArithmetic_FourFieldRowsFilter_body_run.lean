-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_body_run
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.body_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:12:08.67379+00:00
-- url     : https://prove2.me/theorems/4d332307-c4d3-4749-9da8-3f2d7eb16799
-- title:
--   Four Field Rows Filter: body run
-- statement:
--   Actual row-controller instruction, tape simulation, field phase or exact counted transfer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFourFieldRowsFilter.lean#L466-L470
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFourFieldRowsFilter.lean#L466-L470

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
variable (P:Machine)

theorem QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.body_run (C x y:List Bool) (n:ℕ)
 (hn:(fun c=>c.bind (TM2.step P.program))^[n] (some (P.init x))=some (P.halt y)):
 (next P)^[n] (some (embedBody P C (P.init x)))=some (embedBody P C (P.halt y)):= by sorry
