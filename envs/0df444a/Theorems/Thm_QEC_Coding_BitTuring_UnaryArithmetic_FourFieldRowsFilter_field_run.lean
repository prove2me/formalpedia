-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_field_run
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.field_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:07:38.721091+00:00
-- url     : https://prove2.me/theorems/d62bc1e1-92e0-4ca5-9fc1-8641678be98f
-- title:
--   Four Field Rows Filter: field run
-- statement:
--   Actual row-controller instruction, tape simulation, field phase or exact counted transfer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFourFieldRowsFilter.lean#L391-L403
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFourFieldRowsFilter.lean#L391-L403

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
variable (P:Machine)

theorem QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.field_run (hio:P.input≠P.output) (k:Fin 4) (f:Bool) (h:Option Bool) (a:ℕ)
 (I O H C B:List Bool):
 (fun c:Option (TM2.Cfg (fun _:Stack P=>Bool) (Label P) (Var P))=>c.bind (TM2.step (program P)))^[a+1]
  (some (cfg P ⟨5+k.val,by omega⟩ f h I (unary a++false::O) H C B))=
 some (cfg P ⟨6+k.val,by omega⟩ f (some false) I O H (pushed f (unary a++[false]) C) B):= by sorry
