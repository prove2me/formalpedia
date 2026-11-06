-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_agEvaluationLinearMap_apply
-- name    : QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:22:24.742051+00:00
-- url     : https://prove2.me/theorems/2c34b6b4-e519-41d0-82f2-43b4cb60eb32
-- title:
--   Algebraic Geometry: ag Evaluation Linear Map apply
-- statement:
--   Coordinate formula for the evaluation linear map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/Evaluation.lean#L206-L211
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/Evaluation.lean#L206-L211

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

theorem QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap_apply (G : Divisor (GlobalPlace k F))
    (Q : ι → RationalPlace k F) (hG : ∀ i, G (Q i).place = 0)
    (f : GlobalPlace.riemannRochSubmodule G) (i : ι) :
    agEvaluationLinearMap G Q hG f i =
      (Q i).evaluateRegular (f : F) (evaluationRegularity G Q hG f i) := by sorry

attribute [defeq] QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap_apply
