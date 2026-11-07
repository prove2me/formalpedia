-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_inv_splittingY_smul_wrap_boundary
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.inv_splittingY_smul_wrap_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:04:10.224179+00:00
-- url     : https://prove2.me/theorems/a6e7521e-f01d-4b9d-9397-3adf0194c12f
-- title:
--   Cartwright Steger: inv splitting Y smul wrap boundary
-- statement:
--   Multiplication by `y⁻¹` cancels the retained cyclic boundary exactly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L1055-L1069
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L1055-L1069

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.inv_splittingY_smul_wrap_boundary
    (P : BasePrime) (r : Rank)
    (S D : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r)) :
    -D + (splittingY P r)⁻¹ •
        (S + (onePlusY P r) • D - D) =
      (splittingY P r)⁻¹ • S := by sorry
