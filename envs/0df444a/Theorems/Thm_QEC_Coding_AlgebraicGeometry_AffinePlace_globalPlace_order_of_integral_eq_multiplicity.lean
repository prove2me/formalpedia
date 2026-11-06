-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_globalPlace_order_of_integral_eq_multiplicity
-- name    : QEC.Coding.AlgebraicGeometry.AffinePlace.globalPlace_order_of_integral_eq_multiplicity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:36:26.988211+00:00
-- url     : https://prove2.me/theorems/1a4d1c1d-f675-48ba-9303-7f03ac89d07b
-- title:
--   Affine Place: global Place order of integral eq multiplicity
-- statement:
--   The global-place order convention turns the adic valuation of a nonzero
--   integral element into its positive prime-ideal multiplicity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/AffineGlobalPlace.lean#L82-L89
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/AffineGlobalPlace.lean#L82-L89

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

theorem QEC.Coding.AlgebraicGeometry.AffinePlace.globalPlace_order_of_integral_eq_multiplicity (P : carrier k F)
    {x : _root_.FunctionField.ringOfIntegers k F} (hx : x ≠ 0) :
    GlobalPlace.order (globalPlace k F P)
      (algebraMap (_root_.FunctionField.ringOfIntegers k F) F x) =
        (multiplicity P.asIdeal (Ideal.span {x}) : ℤ) := by sorry
