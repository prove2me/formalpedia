-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_raw_length_le
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection.raw_length_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:07:44.330279+00:00
-- url     : https://prove2.me/theorems/46ac8f65-179c-4b45-b6a8-d46345371e0e
-- title:
--   Field Projection: raw length le
-- statement:
--   Proved actual execution phase or mathematical tape invariant for the complete program.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFieldProjection.lean#L344-L345
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFieldProjection.lean#L344-L345

import Definitions.Def_QEC_Coding_BitTuring_UnaryOutputEquality
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
variable (n:ℕ) (keep:Fin (n+1)→Bool)

theorem QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection.raw_length_le (xs:List ℕ) : (raw xs).length≤(stream xs).length := by sorry
