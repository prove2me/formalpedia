-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_agEvaluation_one_mem
-- name    : QEC.Coding.AlgebraicGeometry.agEvaluation_one_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:26:48.35965+00:00
-- url     : https://prove2.me/theorems/6ed15b81-fc0e-4819-8b17-84b1d141d5a1
-- title:
--   Algebraic Geometry: ag Evaluation one mem
-- statement:
--   The all-ones word is in an evaluation code whenever the defining divisor
--   is coefficientwise nonnegative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/Code.lean#L92-L106
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/Code.lean#L92-L106

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_Evaluation
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_Code
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators Polynomial RatFunc WithZero
variable {k F ι : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
variable [Fintype ι]

theorem QEC.Coding.AlgebraicGeometry.agEvaluation_one_mem [Fintype k]
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hG : ∀ i, G (Q i).place = 0) (hGnonnegative : Divisor.Nonnegative G) :
    (1 : Word k ι) ∈ (agEvaluationCode G Q hG).carrier := by sorry
