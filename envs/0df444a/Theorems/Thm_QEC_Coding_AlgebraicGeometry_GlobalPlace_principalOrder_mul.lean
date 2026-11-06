-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_principalOrder_mul
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.principalOrder_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:28:11.233395+00:00
-- url     : https://prove2.me/theorems/9aa0601a-731f-473b-abf8-128bb6d07eb3
-- title:
--   Global Place: principal Order mul
-- statement:
--   Principal-order families add under multiplication of nonzero functions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/PrincipalOrder.lean#L31-L36
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/PrincipalOrder.lean#L31-L36

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_PrincipalOrder
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.principalOrder_mul (f g : Fˣ) :
    principalOrder (k := k) (F := F) (f * g) =
      principalOrder (k := k) (F := F) f + principalOrder (k := k) (F := F) g := by sorry
