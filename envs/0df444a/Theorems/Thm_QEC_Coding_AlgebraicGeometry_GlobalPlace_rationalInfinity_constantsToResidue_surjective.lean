-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalInfinity_constantsToResidue_surjective
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalInfinity_constantsToResidue_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:18:33.362388+00:00
-- url     : https://prove2.me/theorems/1be4e191-1f5f-4351-8ee4-4ab06a321e57
-- title:
--   Global Place: rational Infinity constants To Residue surjective
-- statement:
--   Every residue class at the rational-function infinity place is the
--   reduction of a constant.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/InfinityResidue.lean#L133-L138
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/InfinityResidue.lean#L133-L138

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_RationalBaseInfinityCancellation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_InfinityResidue
set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k : Type*} [Field k] [Finite k]

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalInfinity_constantsToResidue_surjective :
    Function.Surjective (constantsToResidue (rationalInfinity k)) := by sorry
