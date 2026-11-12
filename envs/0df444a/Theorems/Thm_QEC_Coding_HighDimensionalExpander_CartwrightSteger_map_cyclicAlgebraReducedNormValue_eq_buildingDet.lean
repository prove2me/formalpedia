-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_map_cyclicAlgebraReducedNormValue_eq_buildingDet
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_cyclicAlgebraReducedNormValue_eq_buildingDet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:23:39.954264+00:00
-- url     : https://prove2.me/theorems/588d9208-9257-409d-b314-2acb09790bb2
-- title:
--   Cartwright Steger: map cyclic Algebra Reduced Norm Value eq building Det
-- statement:
--   Exact compatibility of the construction-owned reduced norm with the
--   distinguished building-place splitting.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/IntrinsicNorm.lean#L575-L597
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/IntrinsicNorm.lean#L575-L597

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_GlobalNormOneBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_SplittingFieldDescent
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_MatrixAlgebraNorm
import Mathlib.Algebra.Polynomial.Roots
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_IntrinsicNorm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped Polynomial

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_cyclicAlgebraReducedNormValue_eq_buildingDet
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    algebraMap (FunctionField P) (BuildingLocalField P)
        (cyclicAlgebraReducedNormValue P r x) =
      Matrix.det (cyclicAlgebraToBuilding P r x) := by sorry
