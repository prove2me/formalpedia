-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_PrefixProjection_fields_all
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection.fields_all
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:09:15.791194+00:00
-- url     : https://prove2.me/theorems/ec250235-5216-4f19-9fca-7836b5439d53
-- title:
--   Prefix Projection: fields all
-- statement:
--   Actual finite instructions or proved configuration, execution, budget, faithful encoding or source certificate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryPrefixProjection.lean#L261-L264
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryPrefixProjection.lean#L261-L264

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition FieldProjection
variable (n:ℕ) (keep:Fin (n+1)→Bool)
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
variable (n:ℕ) (keep:Fin (n+1)→Bool)

theorem QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection.fields_all (i:ℕ) (xs:List ℕ):fields n (allMask n) i xs=xs:= by sorry
