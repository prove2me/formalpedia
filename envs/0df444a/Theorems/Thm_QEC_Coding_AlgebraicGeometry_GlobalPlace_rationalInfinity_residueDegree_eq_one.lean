-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalInfinity_residueDegree_eq_one
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalInfinity_residueDegree_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:18:32.870635+00:00
-- url     : https://prove2.me/theorems/b2c2631b-db14-4a1d-b344-ea98025d71f2
-- title:
--   Global Place: rational Infinity residue Degree eq one
-- statement:
--   The normalized rational-function infinity place has residue degree one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/InfinityResidue.lean#L141-L152
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/InfinityResidue.lean#L141-L152

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_RationalBaseInfinityCancellation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_InfinityResidue
set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k : Type*} [Field k] [Finite k]

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalInfinity_residueDegree_eq_one :
    residueDegree (k := k) (F := RatFunc k) (rationalInfinity k) = 1 := by sorry
