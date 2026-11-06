-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseAffinePlace_rationalInvolution_X
-- name    : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.rationalInvolution_X
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:42:55.274573+00:00
-- url     : https://prove2.me/theorems/50045dd3-6e45-453a-a68c-f0e367075bac
-- title:
--   Inverse Affine Place: rational Involution X
-- statement:
--   The rational involution sends the variable to its reciprocal.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/InverseAffinePlace.lean#L68-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/InverseAffinePlace.lean#L68-L70

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseChart
import Mathlib.FieldTheory.Separable
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.InverseAffinePlace
open scoped IntermediateField Polynomial RatFunc
variable (k : Type*) [Field k]

theorem QEC.Coding.AlgebraicGeometry.InverseAffinePlace.rationalInvolution_X :
    rationalInvolution k RatFunc.X = (RatFunc.X : RatFunc k)⁻¹ := by sorry
