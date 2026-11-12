-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_localUnitOrder_buildingLocalYUnit
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.localUnitOrder_buildingLocalYUnit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:44:11.428622+00:00
-- url     : https://prove2.me/theorems/5a22e1b1-ae44-43ee-9218-11e457a08556
-- title:
--   Cartwright Steger: local Unit Order building Local YUnit
-- statement:
--   The Cartwright Steger construction uses the local Unit Order building Local YUnit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/Stabilizer.lean#L80-L91
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/Stabilizer.lean#L80-L91

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_LatticeBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_RepresentationKernel
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Stabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.localUnitOrder_buildingLocalYUnit
    (P : BasePrime) :
    SphericalHecke.localUnitOrder (buildingLocalYUnit P) = 1 := by sorry
