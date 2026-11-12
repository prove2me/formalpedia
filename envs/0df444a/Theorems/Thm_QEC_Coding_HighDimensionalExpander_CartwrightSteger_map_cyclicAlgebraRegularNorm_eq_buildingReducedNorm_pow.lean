-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_map_cyclicAlgebraRegularNorm_eq_buildingReducedNorm_pow
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_cyclicAlgebraRegularNorm_eq_buildingReducedNorm_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:26:30.654324+00:00
-- url     : https://prove2.me/theorems/3a858b2b-9787-42bc-8a74-be7889219451
-- title:
--   Cartwright Steger: map cyclic Algebra Regular Norm eq building Reduced Norm pow
-- statement:
--   For every global cyclic-algebra unit, its building-place reduced norm
--   has `d`-th power equal to the scalar extension of the intrinsic regular
--   norm.  This comparison is valid on all units and does not assume equality of
--   the reduced norms obtained from different splittings.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/IntrinsicNorm.lean#L74-L97
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/IntrinsicNorm.lean#L74-L97

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_GlobalNormOneBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_SplittingFieldDescent
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_MatrixAlgebraNorm
import Mathlib.Algebra.Polynomial.Roots
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_IntrinsicNorm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped Polynomial

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_cyclicAlgebraRegularNorm_eq_buildingReducedNorm_pow
    (P : BasePrime) (r : Rank) (u : (CyclicAlgebra P r)ˣ) :
    algebraMap (FunctionField P) (BuildingLocalField P)
        (cyclicAlgebraRegularNorm P r (u : CyclicAlgebra P r)) =
      ((cyclicAlgebraBuildingReducedNorm P r u :
          (BuildingLocalField P)ˣ) : BuildingLocalField P) ^
        r.matrixRank := by sorry
