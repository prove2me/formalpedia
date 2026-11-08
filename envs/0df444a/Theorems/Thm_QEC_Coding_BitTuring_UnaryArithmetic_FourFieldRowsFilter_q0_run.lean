-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_q0_run
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.q0_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:05:39.186714+00:00
-- url     : https://prove2.me/theorems/a1f458ff-6add-4a3d-a9b4-48adb743ad83
-- title:
--   Four Field Rows Filter: q0 run
-- statement:
--   Actual row-controller instruction, tape simulation, field phase or exact counted transfer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFourFieldRowsFilter.lean#L296-L306
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFourFieldRowsFilter.lean#L296-L306

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
variable (P:Machine)

theorem QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.q0_run (hio:P.input≠P.output) (f:Bool) (h:Option Bool) (q:ℕ) (I O H C B:List Bool):
 (fun c:Option (TM2.Cfg (fun _:Stack P=>Bool) (Label P) (Var P))=>c.bind (TM2.step (program P)))^[q+1] (some (cfg P 0 f h (unary q++false::I) O H C B))=
 some (cfg P 1 f (some false) I O ((unary q++[false]).reverse++H) C B):= by sorry
