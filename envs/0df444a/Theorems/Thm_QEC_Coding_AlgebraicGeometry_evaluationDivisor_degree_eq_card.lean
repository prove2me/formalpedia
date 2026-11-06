-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_evaluationDivisor_degree_eq_card
-- name    : QEC.Coding.AlgebraicGeometry.evaluationDivisor_degree_eq_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:22:23.327553+00:00
-- url     : https://prove2.me/theorems/3eb4b785-7204-4f2a-9047-a134d0df09e2
-- title:
--   Algebraic Geometry: evaluation Divisor degree eq card
-- statement:
--   The full evaluation divisor has degree the number of coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/Evaluation.lean#L123-L131
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/Evaluation.lean#L123-L131

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

theorem QEC.Coding.AlgebraicGeometry.evaluationDivisor_degree_eq_card
    [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (Q : ι → RationalPlace k F) :
    Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
        (evaluationDivisor Q) = Fintype.card ι := by sorry
