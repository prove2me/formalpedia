-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_evaluationZero_mem_riemannRochSubmodule_sub
-- name    : QEC.Coding.AlgebraicGeometry.evaluationZero_mem_riemannRochSubmodule_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:22:33.482308+00:00
-- url     : https://prove2.me/theorems/224c8408-f377-4d2c-aa0d-fb2636f5fede
-- title:
--   Algebraic Geometry: evaluation Zero mem riemann Roch Submodule sub
-- statement:
--   The full-zero special case used by the evaluation-map kernel argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/Evaluation.lean#L264-L274
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/Evaluation.lean#L264-L274

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

theorem QEC.Coding.AlgebraicGeometry.evaluationZero_mem_riemannRochSubmodule_sub
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (hG : ∀ i, G (Q i).place = 0)
    (f : GlobalPlace.riemannRochSubmodule G)
    (hzero : agEvaluationLinearMap G Q hG f = 0) :
    (f : F) ∈ GlobalPlace.riemannRochSubmodule (G - evaluationDivisor Q) := by sorry
