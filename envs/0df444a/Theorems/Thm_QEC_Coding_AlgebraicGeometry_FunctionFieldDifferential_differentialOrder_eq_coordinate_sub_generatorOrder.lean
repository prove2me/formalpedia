-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differentialOrder_eq_coordinate_sub_generatorOrder
-- name    : QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialOrder_eq_coordinate_sub_generatorOrder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:23:38.993114+00:00
-- url     : https://prove2.me/theorems/f197d230-a198-46a7-ac58-07a5508e0729
-- title:
--   Function Field Differential: differential Order eq coordinate sub generator Order
-- statement:
--   The nonzero differential order is the order of its coordinate minus the
--   order of any actual local principal-cutoff generator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/CanonicalDifferential.lean#L601-L608
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/CanonicalDifferential.lean#L601-L608

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_GlobalPrincipalDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_CanonicalDifferential
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open scoped RatFunc
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

theorem QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialOrder_eq_coordinate_sub_generatorOrder (P : GlobalPlace k F)
    (omega : Differential k F) (homega : omega ≠ 0) {a : F}
    (ha : IsLocalDerivativeLatticePrincipalCutoff (k := k) (F := F) P a) :
    differentialOrder (k := k) (F := F) P omega homega =
      P.order (functionFieldDifferentialCoordinate (k := k) (F := F) omega) -
        P.order a := by sorry
