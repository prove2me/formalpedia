-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_copy9_run
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.copy9_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:07:22.898113+00:00
-- url     : https://prove2.me/theorems/5e107b41-dad9-4d68-ac9c-ebd25c902821
-- title:
--   Four Field Rows Filter: copy9 run
-- statement:
--   Actual row-controller instruction, tape simulation, field phase or exact counted transfer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFourFieldRowsFilter.lean#L331-L340
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFourFieldRowsFilter.lean#L331-L340

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
variable (P:Machine)

theorem QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.copy9_run (hio:P.input≠P.output) (f:Bool) (h:Option Bool) (I O H C B:List Bool):
 (fun c:Option (TM2.Cfg (fun _:Stack P=>Bool) (Label P) (Var P))=>c.bind (TM2.step (program P)))^[O.length+1] (some (cfg P 9 f h I O H C B))=
 some (cfg P 10 f none I [] H C (O.reverse++B)):= by sorry
