-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_stream_injective
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection.stream_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:07:40.688992+00:00
-- url     : https://prove2.me/theorems/212241c3-4aa6-46cc-b626-139e817b97dc
-- title:
--   Field Projection: stream injective
-- statement:
--   Proved actual execution phase or mathematical tape invariant for the complete program.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFieldProjection.lean#L256-L274
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFieldProjection.lean#L256-L274

import Definitions.Def_QEC_Coding_BitTuring_UnaryOutputEquality
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
open Turing StateTransition
variable (n:ℕ) (keep:Fin (n+1) → Bool)

theorem QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection.stream_injective : Function.Injective stream := by sorry
