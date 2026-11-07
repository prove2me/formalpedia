-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingFrobeniusMatrix_mul_buildingConstantMatrix
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingFrobeniusMatrix_mul_buildingConstantMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:51:29.227376+00:00
-- url     : https://prove2.me/theorems/64f2ff69-5765-4e1c-bf7f-9dbee2ad2561
-- title:
--   Cartwright Steger: building Frobenius Matrix mul building Constant Matrix
-- statement:
--   The Cartwright Steger construction uses the building Frobenius Matrix mul building Constant Matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingAction.lean#L231-L248
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingAction.lean#L231-L248

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingFrobeniusMatrix_mul_buildingConstantMatrix
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r) :
    buildingFrobeniusMatrix P r * buildingConstantMatrix P r c =
      buildingConstantMatrix P r (constantFrobenius P r c) *
        buildingFrobeniusMatrix P r := by sorry
