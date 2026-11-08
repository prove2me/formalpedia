-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_entry_run
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.entry_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:12:01.110573+00:00
-- url     : https://prove2.me/theorems/e8c44198-a333-454d-8c38-b72c42d7f22c
-- title:
--   Four Field Rows Filter: entry run
-- statement:
--   Actual row-controller instruction, tape simulation, field phase or exact counted transfer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFourFieldRowsFilter.lean#L449-L464
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFourFieldRowsFilter.lean#L449-L464

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
variable (P:Machine)

theorem QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.entry_run (hio:P.input≠P.output) (q:ℕ) (s C:List Bool) (hs:s≠[]):
 (next P)^[2*(q+1)+2] (some (cfg P 0 false none (qword q++s) [] [] C []))=
 some (embedBody P C (P.init (qword q++s))):= by sorry
