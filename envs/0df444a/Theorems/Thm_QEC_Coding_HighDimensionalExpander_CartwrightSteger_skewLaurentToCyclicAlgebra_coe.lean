-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentToCyclicAlgebra_coe
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentToCyclicAlgebra_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:25:49.246998+00:00
-- url     : https://prove2.me/theorems/ca29700f-6470-4229-94df-144212fb7c52
-- title:
--   Cartwright Steger: skew Laurent To Cyclic Algebra coe
-- statement:
--   The Cartwright Steger construction uses the skew Laurent To Cyclic Algebra coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewCompatibility.lean#L68-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewCompatibility.lean#L68-L72

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_OrderUnitReconstruction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingSkewRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewCompatibility
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentToCyclicAlgebra_coe
    (P : BasePrime) (r : Rank)
    (f : CartwrightStegerSkewLaurentRing P r) :
    (skewLaurentToCyclicAlgebra P r f).1 =
      skewLaurentToGlobalMatrix P r f := by sorry

attribute [defeq] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentToCyclicAlgebra_coe
