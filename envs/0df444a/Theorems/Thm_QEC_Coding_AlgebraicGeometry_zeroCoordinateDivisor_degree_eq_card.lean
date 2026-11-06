-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_zeroCoordinateDivisor_degree_eq_card
-- name    : QEC.Coding.AlgebraicGeometry.zeroCoordinateDivisor_degree_eq_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:23:06.307442+00:00
-- url     : https://prove2.me/theorems/a578d2eb-9774-4854-86a0-3de4a456be3f
-- title:
--   Algebraic Geometry: zero Coordinate Divisor degree eq card
-- statement:
--   The selected-coordinate divisor has degree the cardinality of its finite
--   index set: every selected rational global place has the genuine all-place
--   residue degree one, supplied by `RationalPlace.globalResidueDegree_eq_one`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/Evaluation.lean#L97-L120
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/Evaluation.lean#L97-L120

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

theorem QEC.Coding.AlgebraicGeometry.zeroCoordinateDivisor_degree_eq_card
    [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (Q : ι → RationalPlace k F) (S : Finset ι) :
    Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
        (zeroCoordinateDivisor Q S) = S.card := by sorry
