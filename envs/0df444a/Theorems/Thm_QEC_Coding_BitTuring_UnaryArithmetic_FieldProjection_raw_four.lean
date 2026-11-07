-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_raw_four
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection.raw_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:08:26.76169+00:00
-- url     : https://prove2.me/theorems/d9f65008-b87d-4156-8ad4-1f1ca8c78064
-- title:
--   Field Projection: raw four
-- statement:
--   Proved actual execution phase or mathematical tape invariant for the complete program.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFieldProjection.lean#L348-L350
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFieldProjection.lean#L348-L350

import Definitions.Def_QEC_Coding_BitTuring_UnaryOutputEquality
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
variable (n:ℕ) (keep:Fin (n+1)→Bool)

theorem QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection.raw_four (a b c d:ℕ) : raw [a,b,c,d]=
    unary a++false::(unary b++false::(unary c++false::unary d)) := by sorry
