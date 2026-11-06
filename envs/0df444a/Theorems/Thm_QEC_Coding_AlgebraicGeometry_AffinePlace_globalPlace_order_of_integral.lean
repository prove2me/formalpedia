-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_globalPlace_order_of_integral
-- name    : QEC.Coding.AlgebraicGeometry.AffinePlace.globalPlace_order_of_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:10:06.3772+00:00
-- url     : https://prove2.me/theorems/458392e1-97ff-4005-a4a3-9dd4f17bad5d
-- title:
--   Affine Place: global Place order of integral
-- statement:
--   For an integral element, the packaged global order is the negative
--   logarithm of its genuine adic valuation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/AffineGlobalPlace.lean#L71-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/AffineGlobalPlace.lean#L71-L78

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffineGlobalPlace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
open QEC.Coding.AlgebraicGeometry.AffinePlace
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.AffinePlace._p2m_local_instance_439b1c180e_47

theorem QEC.Coding.AlgebraicGeometry.AffinePlace.globalPlace_order_of_integral (P : carrier k F)
    (x : _root_.FunctionField.ringOfIntegers k F) :
    GlobalPlace.order (globalPlace k F P)
      (algebraMap (_root_.FunctionField.ringOfIntegers k F) F x) =
        -WithZero.log (P.intValuation x) := by sorry
