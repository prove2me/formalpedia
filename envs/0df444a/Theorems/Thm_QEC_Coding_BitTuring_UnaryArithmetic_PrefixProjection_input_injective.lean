-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_PrefixProjection_input_injective
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection.input_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:11:10.608588+00:00
-- url     : https://prove2.me/theorems/e3a927ae-aabf-4e66-9c53-2b41c17f6e15
-- title:
--   Prefix Projection: input injective
-- statement:
--   Actual finite instructions or proved configuration, execution, budget, faithful encoding or source certificate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryPrefixProjection.lean#L239-L243
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryPrefixProjection.lean#L239-L243

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryOutputEquality_input_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition FieldProjection
variable (n:ℕ) (keep:Fin (n+1)→Bool)
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
variable (n:ℕ) (keep:Fin (n+1)→Bool)

theorem QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection.input_injective:Function.Injective (input n):= by sorry
