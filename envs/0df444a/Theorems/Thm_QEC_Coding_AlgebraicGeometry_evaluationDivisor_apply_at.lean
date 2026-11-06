-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_evaluationDivisor_apply_at
-- name    : QEC.Coding.AlgebraicGeometry.evaluationDivisor_apply_at
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:24:33.905016+00:00
-- url     : https://prove2.me/theorems/bd18984d-c2c7-47c2-b678-cd8f6624382c
-- title:
--   Algebraic Geometry: evaluation Divisor apply at
-- statement:
--   The full evaluation divisor has coefficient one at every coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/Evaluation.lean#L82-L86
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/Evaluation.lean#L82-L86

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_NegativeDegreeVanishing
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlaceDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_Evaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators Polynomial RatFunc WithZero
variable {k F ι : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
variable [Fintype ι]

theorem QEC.Coding.AlgebraicGeometry.evaluationDivisor_apply_at (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place) (i : ι) :
    evaluationDivisor Q (Q i).place = 1 := by sorry
