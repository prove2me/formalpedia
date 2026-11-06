-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_zeroCoordinateDivisor_apply_at
-- name    : QEC.Coding.AlgebraicGeometry.zeroCoordinateDivisor_apply_at
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:22:35.538015+00:00
-- url     : https://prove2.me/theorems/95d05db8-15e1-4afb-8af0-83f9e480398e
-- title:
--   Algebraic Geometry: zero Coordinate Divisor apply at
-- statement:
--   At a selected coordinate, pairwise distinctness makes the reduced divisor
--   coefficient exactly one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/Evaluation.lean#L52-L66
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/Evaluation.lean#L52-L66

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

theorem QEC.Coding.AlgebraicGeometry.zeroCoordinateDivisor_apply_at (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place) (S : Finset ι)
    {i : ι} (hi : i ∈ S) :
    zeroCoordinateDivisor Q S (Q i).place = 1 := by sorry
