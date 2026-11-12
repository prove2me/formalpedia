-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraReducedNorm_baseChange_eq_buildingReducedNorm
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraReducedNorm_baseChange_eq_buildingReducedNorm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:24:13.067166+00:00
-- url     : https://prove2.me/theorems/2390330e-e4d3-4e11-968e-9d3778a8f54a
-- title:
--   Cartwright Steger: cyclic Algebra Reduced Norm base Change eq building Reduced Norm
-- statement:
--   On units, the base-field reduced norm becomes the existing concrete
--   building reduced norm under scalar extension.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/IntrinsicNorm.lean#L601-L628
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/IntrinsicNorm.lean#L601-L628

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_GlobalNormOneBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_SplittingFieldDescent
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_MatrixAlgebraNorm
import Mathlib.Algebra.Polynomial.Roots
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_IntrinsicNorm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped Polynomial

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraReducedNorm_baseChange_eq_buildingReducedNorm
    (P : BasePrime) (r : Rank) (u : (CyclicAlgebra P r)ˣ) :
    Units.map (functionFieldToBuildingLocalField P)
        (cyclicAlgebraReducedNorm P r u) =
      cyclicAlgebraBuildingReducedNorm P r u := by sorry
