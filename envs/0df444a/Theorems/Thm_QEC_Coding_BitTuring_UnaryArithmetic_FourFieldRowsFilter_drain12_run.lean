-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_drain12_run
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.drain12_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:07:40.462124+00:00
-- url     : https://prove2.me/theorems/7f5509d6-b778-4a6d-837c-4574b7016104
-- title:
--   Four Field Rows Filter: drain12 run
-- statement:
--   Actual row-controller instruction, tape simulation, field phase or exact counted transfer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFourFieldRowsFilter.lean#L364-L372
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFourFieldRowsFilter.lean#L364-L372

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
variable (P:Machine)

theorem QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.drain12_run (hio:P.input≠P.output) (f:Bool) (h:Option Bool) (I O H C B:List Bool):
 (fun c:Option (TM2.Cfg (fun _:Stack P=>Bool) (Label P) (Var P))=>c.bind (TM2.step (program P)))^[H.length+1] (some (cfg P 12 f h I O H C B))=
 some (cfg P 13 f none I O [] C B):= by sorry
