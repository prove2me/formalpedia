-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalPlace_evaluateRegular_algebraMap
-- name    : QEC.Coding.AlgebraicGeometry.RationalPlace.evaluateRegular_algebraMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:44:26.483507+00:00
-- url     : https://prove2.me/theorems/2e0c2d65-4466-4bfe-aaec-24af8370a99e
-- title:
--   Rational Place: evaluate Regular algebra Map
-- statement:
--   The regular-function evaluation formulation of constant preservation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RationalPlace.lean#L128-L131
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RationalPlace.lean#L128-L131

import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.RationalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]

theorem QEC.Coding.AlgebraicGeometry.RationalPlace.evaluateRegular_algebraMap (Q : RationalPlace k F) (a : k) :
    Q.evaluateRegular (algebraMap k F a) (Q.constants_regular a) = a := by sorry
