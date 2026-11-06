-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_principalOrder_inv
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.principalOrder_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:28:08.452368+00:00
-- url     : https://prove2.me/theorems/60b534c0-eeee-4f8c-bc8e-ecd34809ef1e
-- title:
--   Global Place: principal Order inv
-- statement:
--   Principal-order families negate under inversion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/PrincipalOrder.lean#L39-L42
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/PrincipalOrder.lean#L39-L42

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_PrincipalOrder
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.principalOrder_inv (f : Fˣ) :
    principalOrder (k := k) (F := F) f⁻¹ = -principalOrder (k := k) (F := F) f := by sorry
