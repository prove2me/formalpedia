-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingCyclicGeneratorMatrix_mul_buildingConstantMatrix
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingCyclicGeneratorMatrix_mul_buildingConstantMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:51:38.205109+00:00
-- url     : https://prove2.me/theorems/656207d5-dd51-4e29-a593-db96f96132ec
-- title:
--   Cartwright Steger: building Cyclic Generator Matrix mul building Constant Matrix
-- statement:
--   The Cartwright Steger construction uses the building Cyclic Generator Matrix mul building Constant Matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingAction.lean#L365-L371
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingAction.lean#L365-L371

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_FrobeniusCharpoly
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingCyclicGeneratorMatrix_mul_buildingConstantMatrix
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r) :
    buildingCyclicGeneratorMatrix P r * buildingConstantMatrix P r c =
      buildingConstantMatrix P r (constantFrobenius P r c) *
        buildingCyclicGeneratorMatrix P r := by sorry
