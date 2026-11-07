-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_raw_triple
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection.raw_triple
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:08:30.881184+00:00
-- url     : https://prove2.me/theorems/987f5e03-2def-4c75-a760-c96f0f82d139
-- title:
--   Field Projection: raw triple
-- statement:
--   Proved actual execution phase or mathematical tape invariant for the complete program.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFieldProjection.lean#L328-L330
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFieldProjection.lean#L328-L330

import Definitions.Def_QEC_Coding_BitTuring_UnaryOutputEquality
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection

theorem QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection.raw_triple (a b q:ℕ) : raw [a,b,q]=FactorTest.tripleInput a b q := by sorry
