-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_field_sep
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.field_sep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:07:15.61155+00:00
-- url     : https://prove2.me/theorems/419df658-4e90-49d5-9898-610061b57c78
-- title:
--   Four Field Rows Filter: field sep
-- statement:
--   Actual row-controller instruction, tape simulation, field phase or exact counted transfer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFourFieldRowsFilter.lean#L282-L290
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFourFieldRowsFilter.lean#L282-L290

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring Turing StateTransition
variable (P:Machine)

theorem QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.field_sep (hio:P.input≠P.output) (k:Fin 4) (f:Bool) (h:Option Bool)
 (I O H C B:List Bool):
 TM2.step (program P) (cfg P ⟨5+k.val,by omega⟩ f h I (false::O) H C B)=
 some (cfg P ⟨6+k.val,by omega⟩ f (some false) I O H (if f then C else false::C) B):= by sorry
