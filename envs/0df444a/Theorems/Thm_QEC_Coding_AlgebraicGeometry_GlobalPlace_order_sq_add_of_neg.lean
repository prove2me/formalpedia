-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_sq_add_of_neg
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.order_sq_add_of_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:11:55.096194+00:00
-- url     : https://prove2.me/theorems/ac64ed11-73d2-4785-9fbe-3f7dd3912cbe
-- title:
--   Global Place: order sq add of neg
-- statement:
--   A pole of a quadratic Artin--Schreier coordinate doubles its order in
--   the right-hand side: cancellation cannot occur between unequal orders.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/ArtinSchreierOrder.lean#L19-L38
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/ArtinSchreierOrder.lean#L19-L38

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Mathlib.Tactic.Ring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ArtinSchreierOrder
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
  [Algebra k K] [Algebra k L]

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.order_sq_add_of_neg (Q : GlobalPlace k L) (y : L)
    (hy : Q.order y < 0) : Q.order (y ^ 2 + y) = 2 * Q.order y := by sorry
