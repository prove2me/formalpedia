-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingConstantMatrix_mul
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingConstantMatrix_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:04:53.897619+00:00
-- url     : https://prove2.me/theorems/96ff2299-6767-4b18-88ec-39f8d6c05031
-- title:
--   Cartwright Steger: building Constant Matrix mul
-- statement:
--   The Cartwright Steger construction uses the building Constant Matrix mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingConstantKernel.lean#L26-L35
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingConstantKernel.lean#L26-L35

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_CompactNormalForm
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingConstantKernel
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingConstantMatrix_mul
    (P : BasePrime) (r : Rank) (c d : ConstantExtension P r) :
    buildingConstantMatrix P r c * buildingConstantMatrix P r d =
      buildingConstantMatrix P r (c * d) := by sorry
