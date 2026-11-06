-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_agEvaluation_distance_lower_bound
-- name    : QEC.Coding.AlgebraicGeometry.agEvaluation_distance_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:24:43.159333+00:00
-- url     : https://prove2.me/theorems/90d016ab-853b-435f-9587-d6048f3dcaf3
-- title:
--   Algebraic Geometry: ag Evaluation distance lower bound
-- statement:
--   The elementary source-convention lower bound on the extended minimum
--   distance of the genuine evaluation code.  A negative divisor degree gives a
--   zero code and hence extended distance infinity; the bound consequently uses
--   the literal signed difference before converting it to a natural number.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/Code.lean#L143-L238
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/Code.lean#L143-L238

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_Evaluation
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_Code
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators Polynomial RatFunc WithZero
variable {k F ι : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
variable [Fintype ι]

theorem QEC.Coding.AlgebraicGeometry.agEvaluation_distance_lower_bound
    [Fintype k] [DecidableEq k] [DecidableEq ι]
    [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (hG : ∀ i, G (Q i).place = 0) :
    (Int.toNat ((Fintype.card ι : ℤ) -
      Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G) : WithTop Nat) ≤
      QEC.Coding.HypergraphProduct.extendedMinimumDistance (agEvaluationCode G Q hG) := by sorry
