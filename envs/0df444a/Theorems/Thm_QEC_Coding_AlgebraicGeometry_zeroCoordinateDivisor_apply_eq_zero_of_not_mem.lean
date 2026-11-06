-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_zeroCoordinateDivisor_apply_eq_zero_of_not_mem
-- name    : QEC.Coding.AlgebraicGeometry.zeroCoordinateDivisor_apply_eq_zero_of_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:22:35.82261+00:00
-- url     : https://prove2.me/theorems/a40c36b3-ad67-4c5e-9c3d-b0eac1d7cbfb
-- title:
--   Algebraic Geometry: zero Coordinate Divisor apply eq zero of not mem
-- statement:
--   Away from the selected coordinates, the selected-coordinate divisor has
--   zero coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/Evaluation.lean#L70-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/Evaluation.lean#L70-L79

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

theorem QEC.Coding.AlgebraicGeometry.zeroCoordinateDivisor_apply_eq_zero_of_not_mem (Q : ι → RationalPlace k F)
    (S : Finset ι) (P : GlobalPlace k F)
    (hP : ∀ i ∈ S, (Q i).place ≠ P) :
    zeroCoordinateDivisor Q S P = 0 := by sorry
