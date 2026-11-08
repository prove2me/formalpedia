-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_after_run
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.after_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:12:35.960236+00:00
-- url     : https://prove2.me/theorems/627bacd6-5ba4-4294-a6b3-daff9edef355
-- title:
--   Four Field Rows Filter: after run
-- statement:
--   Actual row-controller instruction, tape simulation, field phase or exact counted transfer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFourFieldRowsFilter.lean#L490-L501
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFourFieldRowsFilter.lean#L490-L501

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
variable (P:Machine)

theorem QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.after_run (hio:P.input≠P.output) (f:Bool) (h:Option Bool) (q:ℕ) (R C:List Bool):
 (next P)^[2*R.length+(q+1)+3]
  (some (cfg P 9 f h [] R (qword q).reverse C []))=
 some (cfg P 0 false none (qword q++R) [] [] C []):= by sorry
