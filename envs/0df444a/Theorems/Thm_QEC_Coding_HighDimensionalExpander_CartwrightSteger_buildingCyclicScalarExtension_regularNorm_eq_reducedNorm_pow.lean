-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingCyclicScalarExtension_regularNorm_eq_reducedNorm_pow
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingCyclicScalarExtension_regularNorm_eq_reducedNorm_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:21:23.874965+00:00
-- url     : https://prove2.me/theorems/7775595f-a8dd-48e4-aff6-3604d503abc9
-- title:
--   Cartwright Steger: building Cyclic Scalar Extension regular Norm eq reduced Norm pow
-- statement:
--   At the building splitting, the intrinsic regular norm is exactly the
--   `d`-th power of the construction's local reduced norm.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/IntrinsicNorm.lean#L44-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/IntrinsicNorm.lean#L44-L68

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_GlobalNormOneBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_SplittingFieldDescent
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_MatrixAlgebraNorm
import Mathlib.Algebra.Polynomial.Roots
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_IntrinsicNorm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped Polynomial

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingCyclicScalarExtension_regularNorm_eq_reducedNorm_pow
    (P : BasePrime) (r : Rank)
    (u : (BuildingCyclicScalarExtension P r)ˣ) :
    Algebra.norm (BuildingLocalField P)
        (u : BuildingCyclicScalarExtension P r) =
      ((buildingCyclicScalarExtensionReducedNorm P r u :
          (BuildingLocalField P)ˣ) : BuildingLocalField P) ^
        r.matrixRank := by sorry
