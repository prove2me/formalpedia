-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGenerator_inv_val
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerGenerator_inv_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:21:23.469273+00:00
-- url     : https://prove2.me/theorems/8ef40961-b9e5-40db-a89e-0a3108b67254
-- title:
--   Cartwright Steger: cartwright Steger Generator inv val
-- statement:
--   The proved inverse expansion for each internally selected generator
--   of the construction-owned global matrix group.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L1263-L1274
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L1263-L1274

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerGenerator_inv_val
    (P : BasePrime) (r : Rank) (x : ConstantProjectiveClass P r) :
    (((cartwrightStegerGenerator P r x)⁻¹ :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) =
      constantConjugatedBInverseExpansion P r
        (constantClassRepresentative P r x) := by sorry
