-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_parse4_run
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.parse4_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:07:48.592876+00:00
-- url     : https://prove2.me/theorems/9ecc14c5-4e77-4078-8e76-c703853ff7ea
-- title:
--   Four Field Rows Filter: parse4 run
-- statement:
--   Actual row-controller instruction, tape simulation, field phase or exact counted transfer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFourFieldRowsFilter.lean#L405-L435
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFourFieldRowsFilter.lean#L405-L435

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
variable (P:Machine)

theorem QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.parse4_run (hio:P.input≠P.output) (xs:List ℕ) (k:Fin 5) (hk:k.val+xs.length=4)
 (f:Bool) (h:Option Bool) (I O H C B:List Bool):
 (fun c:Option (TM2.Cfg (fun _:Stack P=>Bool) (Label P) (Var P))=>c.bind (TM2.step (program P)))^[(stream xs).length]
  (some (cfg P ⟨5+k.val,by omega⟩ f h I (stream xs++O) H C B))=
 some (cfg P 9 f (if xs=[] then h else some false) I O H (pushed f (stream xs) C) B):= by sorry
