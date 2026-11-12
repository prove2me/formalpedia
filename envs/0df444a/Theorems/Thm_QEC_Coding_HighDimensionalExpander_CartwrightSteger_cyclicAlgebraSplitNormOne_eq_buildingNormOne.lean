-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraSplitNormOne_eq_buildingNormOne
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraSplitNormOne_eq_buildingNormOne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:13:40.436219+00:00
-- url     : https://prove2.me/theorems/a7e6dbd2-b861-4737-89b4-c60c46a4aa56
-- title:
--   Cartwright Steger: cyclic Algebra Split Norm One eq building Norm One
-- statement:
--   The two construction-era concrete kernels are the same subgroup, as a
--   consequence rather than an assumption.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/NormOneCompatibility.lean#L77-L81
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/NormOneCompatibility.lean#L77-L81

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_SplitCoordinates
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_NormOneCompatibility
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraSplitNormOne_eq_buildingNormOne
    (P : BasePrime) (r : Rank) :
    CyclicAlgebraSplitNormOne P r = CyclicAlgebraBuildingNormOne P r := by sorry
