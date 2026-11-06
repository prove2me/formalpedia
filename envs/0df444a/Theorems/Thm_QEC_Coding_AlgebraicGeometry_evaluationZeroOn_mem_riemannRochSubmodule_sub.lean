-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_evaluationZeroOn_mem_riemannRochSubmodule_sub
-- name    : QEC.Coding.AlgebraicGeometry.evaluationZeroOn_mem_riemannRochSubmodule_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:22:56.499498+00:00
-- url     : https://prove2.me/theorems/286e6f27-8fca-4dc6-b134-aa595179a4fb
-- title:
--   Algebraic Geometry: evaluation Zero On mem riemann Roch Submodule sub
-- statement:
--   If an evaluated function vanishes on a selected set of coordinates, its
--   valuation bounds improve by one at precisely those rational places.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/Evaluation.lean#L222-L261
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/Evaluation.lean#L222-L261

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

theorem QEC.Coding.AlgebraicGeometry.evaluationZeroOn_mem_riemannRochSubmodule_sub
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (hG : ∀ i, G (Q i).place = 0) (S : Finset ι)
    (f : GlobalPlace.riemannRochSubmodule G)
    (hzero : ∀ i, i ∈ S → agEvaluationLinearMap G Q hG f i = 0) :
    (f : F) ∈ GlobalPlace.riemannRochSubmodule (G - zeroCoordinateDivisor Q S) := by sorry
