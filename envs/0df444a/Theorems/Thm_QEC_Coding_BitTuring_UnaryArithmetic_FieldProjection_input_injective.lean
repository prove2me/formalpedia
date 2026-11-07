-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_input_injective
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection.input_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:10:03.627206+00:00
-- url     : https://prove2.me/theorems/67a5be95-b71a-4c4e-a0cb-8945184bbe15
-- title:
--   Field Projection: input injective
-- statement:
--   The actual encoding distinguishes every domain input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFieldProjection.lean#L282-L283
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFieldProjection.lean#L282-L283

import Definitions.Def_QEC_Coding_BitTuring_UnaryOutputEquality
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Theorems.Thm_QEC_Coding_BitTuring_UnaryOutputEquality_input_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
open Turing StateTransition
variable (n:ℕ) (keep:Fin (n+1) → Bool)

theorem QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection.input_injective : Function.Injective (input n) := by sorry
