-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncFixturePlaces_rationalInfinity_residueDegree_eq_one
-- name    : QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces.rationalInfinity_residueDegree_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:19:57.183021+00:00
-- url     : https://prove2.me/theorems/87ceb7b8-9fbd-4edc-8133-3d7967098879
-- title:
--   Rat Func Fixture Places: rational Infinity residue Degree eq one
-- statement:
--   The actual inverse-chart fibre over `(X)` is rational, and its valuation is
--   the rational-function valuation at infinity.  The generic chart transport
--   therefore makes the canonical global residue degree at infinity equal to one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RatFuncRationalInfinityDegreeTransport.lean#L32-L53
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RatFuncRationalInfinityDegreeTransport.lean#L32-L53

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RatFuncInverseInfinityValuation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RatFuncRationalInfinityDegreeTransport
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces
open scoped Polynomial RatFunc WithZero
open RatFuncInverseInfinityValuation
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces._p2m_local_instance_137389a7d4_9
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces.fixtureOldRationalAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces.fixtureOldPolynomialAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces.fixtureOldScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces.fixtureOldFunctionField
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces.fixtureOldSeparable

theorem QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces.rationalInfinity_residueDegree_eq_one :
    GlobalPlace.residueDegree (k := K) (F := F) (GlobalPlace.rationalInfinity K) = 1 := by sorry
