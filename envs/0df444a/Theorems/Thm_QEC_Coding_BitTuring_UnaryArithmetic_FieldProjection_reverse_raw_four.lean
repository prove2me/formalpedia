-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_reverse_raw_four
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection.reverse_raw_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:07:56.684692+00:00
-- url     : https://prove2.me/theorems/dedfbb72-cdc9-4e4e-a06f-525f7a31380e
-- title:
--   Field Projection: reverse raw four
-- statement:
--   Proved actual execution phase or mathematical tape invariant for the complete program.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFieldProjection.lean#L353-L354
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFieldProjection.lean#L353-L354

import Definitions.Def_QEC_Coding_BitTuring_UnaryOutputEquality
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
variable (n:ℕ) (keep:Fin (n+1)→Bool)

theorem QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection.reverse_raw_four (a b c d:ℕ) : (raw [a,b,c,d]).reverse=raw [d,c,b,a] := by sorry
