-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_parse_current_run
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.parse_current_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:12:33.479719+00:00
-- url     : https://prove2.me/theorems/5043e47a-2209-4c72-8de6-8e24320f9749
-- title:
--   Four Field Rows Filter: parse current run
-- statement:
--   Actual row-controller instruction, tape simulation, field phase or exact counted transfer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFourFieldRowsFilter.lean#L473-L487
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFourFieldRowsFilter.lean#L473-L487

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
variable (P:Machine)

theorem QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.parse_current_run (hio:P.input≠P.output) (f:Bool) (q:ℕ) (xs:List ℕ)
 (hxs:xs.length=4) (R C:List Bool):
 (next P)^[(stream xs).length+(q+1)+1]
  (some (cfg P 3 false none [] (f::(qword q++stream xs++R)) [] C []))=
 some (cfg P 9 f (some false) [] R (qword q).reverse (pushed f (stream xs) C) []):= by sorry
