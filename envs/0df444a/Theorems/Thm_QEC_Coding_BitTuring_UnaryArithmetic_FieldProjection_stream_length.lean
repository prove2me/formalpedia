-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_stream_length
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection.stream_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:07:52.164008+00:00
-- url     : https://prove2.me/theorems/3ebe1cc8-84f7-40c3-80b9-25a07166e358
-- title:
--   Field Projection: stream length
-- statement:
--   Proved actual execution phase or mathematical tape invariant for the complete program.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFieldProjection.lean#L303-L307
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFieldProjection.lean#L303-L307

import Definitions.Def_QEC_Coding_BitTuring_UnaryOutputEquality
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection

theorem QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection.stream_length (xs:List ℕ) : (stream xs).length=xs.sum+xs.length := by sorry
