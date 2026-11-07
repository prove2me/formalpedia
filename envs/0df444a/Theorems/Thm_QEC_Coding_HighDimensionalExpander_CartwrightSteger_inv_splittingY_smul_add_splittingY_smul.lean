-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_inv_splittingY_smul_add_splittingY_smul
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.inv_splittingY_smul_add_splittingY_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:04:03.832395+00:00
-- url     : https://prove2.me/theorems/a05d3df4-e429-45db-9e74-c6cfbc983e7f
-- title:
--   Cartwright Steger: inv splitting Y smul add splitting Y smul
-- statement:
--   The wrapped `y`-multiple becomes the finite correction after applying
--   the outer `y⁻¹`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L1156-L1164
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L1156-L1164

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.inv_splittingY_smul_add_splittingY_smul
    (P : BasePrime) (r : Rank)
    (F K : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r)) :
    (splittingY P r)⁻¹ • (F + (splittingY P r) • K) =
      K + (splittingY P r)⁻¹ • F := by sorry
