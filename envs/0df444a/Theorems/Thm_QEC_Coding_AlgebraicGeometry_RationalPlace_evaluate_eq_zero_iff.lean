-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalPlace_evaluate_eq_zero_iff
-- name    : QEC.Coding.AlgebraicGeometry.RationalPlace.evaluate_eq_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:44:18.103561+00:00
-- url     : https://prove2.me/theorems/f258ac9e-250e-4f07-8091-5c34df5ff387
-- title:
--   Rational Place: evaluate eq zero iff
-- statement:
--   The kernel of rational-place evaluation is exactly the maximal ideal of
--   the valuation ring.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RationalPlace.lean#L99-L104
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RationalPlace.lean#L99-L104

import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.RationalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]

theorem QEC.Coding.AlgebraicGeometry.RationalPlace.evaluate_eq_zero_iff (Q : RationalPlace k F)
    (x : GlobalPlace.valuationRing Q.place) :
    Q.evaluate x = 0 ↔ x ∈ IsLocalRing.maximalIdeal (GlobalPlace.valuationRing Q.place) := by sorry
