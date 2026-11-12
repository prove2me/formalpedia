-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_skewLaurentToCyclicAlgebra
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraToBuilding_skewLaurentToCyclicAlgebra
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:26:19.781547+00:00
-- url     : https://prove2.me/theorems/9df69883-ef15-489f-8e23-eb3fb7495c53
-- title:
--   Cartwright Steger: cyclic Algebra To Building skew Laurent To Cyclic Algebra
-- statement:
--   Applying the building-place algebra map to the global skew image gives
--   the independently constructed building skew representation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewCompatibility.lean#L112-L147
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewCompatibility.lean#L112-L147

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_OrderUnitReconstruction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingSkewRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewCompatibility
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraToBuilding_skewLaurentToCyclicAlgebra
    (P : BasePrime) (r : Rank)
    (f : CartwrightStegerSkewLaurentRing P r) :
    cyclicAlgebraToBuilding P r (skewLaurentToCyclicAlgebra P r f) =
      skewLaurentToBuildingMatrix P r f := by sorry
