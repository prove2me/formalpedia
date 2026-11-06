-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_agEvaluation_injective
-- name    : QEC.Coding.AlgebraicGeometry.agEvaluation_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:23:44.616755+00:00
-- url     : https://prove2.me/theorems/ad4aaf39-5225-4007-bbea-d38f0ac2b57b
-- title:
--   Algebraic Geometry: ag Evaluation injective
-- statement:
--   If the divisor degree is smaller than the number of distinct rational
--   evaluation coordinates, the evaluation map is injective.  The proof uses only
--   the zero-coordinate divisor, its degree-one rational places, and the existing
--   negative-degree vanishing theorem.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/Evaluation.lean#L280-L310
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/Evaluation.lean#L280-L310

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

theorem QEC.Coding.AlgebraicGeometry.agEvaluation_injective
    [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (hG : ∀ i, G (Q i).place = 0)
    (hdegree : Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G <
      Fintype.card ι) :
    Function.Injective (agEvaluationLinearMap G Q hG) := by sorry
