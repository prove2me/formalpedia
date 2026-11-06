-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalPlace_evaluate_constants
-- name    : QEC.Coding.AlgebraicGeometry.RationalPlace.evaluate_constants
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:17:21.669203+00:00
-- url     : https://prove2.me/theorems/5cc162ca-a5b1-4891-943d-38a7081a9366
-- title:
--   Rational Place: evaluate constants
-- statement:
--   Rational-place evaluation fixes constants.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RationalPlace.lean#L122-L125
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RationalPlace.lean#L122-L125

import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.RationalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]

theorem QEC.Coding.AlgebraicGeometry.RationalPlace.evaluate_constants (Q : RationalPlace k F) (a : k) :
    Q.evaluate (GlobalPlace.constantsToValuationRing Q.place a) = a := by sorry
