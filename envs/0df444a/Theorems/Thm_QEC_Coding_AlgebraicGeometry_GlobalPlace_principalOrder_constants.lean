-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_principalOrder_constants
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.principalOrder_constants
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:28:14.321188+00:00
-- url     : https://prove2.me/theorems/de45afec-f325-4958-b2a9-46ee9ed959ca
-- title:
--   Global Place: principal Order constants
-- statement:
--   A nonzero constant has pointwise principal order zero at every global
--   place.  This is derived from finite-field valuation triviality, not stored in
--   the place data.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/PrincipalOrder.lean#L47-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/PrincipalOrder.lean#L47-L50

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_PrincipalOrder
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.principalOrder_constants (a : kˣ) :
    principalOrder (k := k) (F := F) (Units.map (algebraMap k F) a : Fˣ) = 0 := by sorry
