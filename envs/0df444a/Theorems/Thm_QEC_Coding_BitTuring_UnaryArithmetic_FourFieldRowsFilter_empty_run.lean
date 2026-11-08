-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_empty_run
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.empty_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:12:33.126789+00:00
-- url     : https://prove2.me/theorems/652bbd70-1a29-4c2c-a270-411b413f5736
-- title:
--   Four Field Rows Filter: empty run
-- statement:
--   Actual row-controller instruction, tape simulation, field phase or exact counted transfer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFourFieldRowsFilter.lean#L504-L519
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFourFieldRowsFilter.lean#L504-L519

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
variable (P:Machine)

theorem QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.empty_run (hio:P.input≠P.output) (q:ℕ) (C:List Bool):
 (next P)^[2*(q+1)+C.tail.length+4]
  (some (cfg P 0 false none (qword q) [] [] C []))=
 some ((machine P).halt C.tail.reverse):= by sorry
