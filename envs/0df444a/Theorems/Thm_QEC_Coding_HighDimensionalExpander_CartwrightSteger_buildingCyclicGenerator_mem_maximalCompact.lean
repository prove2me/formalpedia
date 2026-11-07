-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingCyclicGenerator_mem_maximalCompact
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingCyclicGenerator_mem_maximalCompact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:51:34.807521+00:00
-- url     : https://prove2.me/theorems/ffb0ad28-fb38-4c14-93e7-7dfc3758c7bd
-- title:
--   Cartwright Steger: building Cyclic Generator mem maximal Compact
-- statement:
--   The Cartwright Steger construction uses the building Cyclic Generator mem maximal Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingAction.lean#L336-L341
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingAction.lean#L336-L341

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingCyclicGenerator_mem_maximalCompact
    (P : BasePrime) (r : Rank) :
    Matrix.ProjGenLinGroup.mk (buildingCyclicGeneratorGL P r) ∈
      SphericalHecke.maximalCompact (BaseField P) r.matrixRank := by sorry
