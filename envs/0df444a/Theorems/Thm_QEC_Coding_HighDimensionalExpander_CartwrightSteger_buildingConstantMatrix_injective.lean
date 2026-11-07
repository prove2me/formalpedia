-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingConstantMatrix_injective
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingConstantMatrix_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:04:52.328132+00:00
-- url     : https://prove2.me/theorems/6e93038a-b12e-48ba-bfe6-601dd1e995c5
-- title:
--   Cartwright Steger: building Constant Matrix injective
-- statement:
--   The Cartwright Steger construction uses the building Constant Matrix injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingConstantKernel.lean#L17-L24
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingConstantKernel.lean#L17-L24

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_CompactNormalForm
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingConstantKernel
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingConstantMatrix_injective
    (P : BasePrime) (r : Rank) :
    Function.Injective (buildingConstantMatrix P r) := by sorry
