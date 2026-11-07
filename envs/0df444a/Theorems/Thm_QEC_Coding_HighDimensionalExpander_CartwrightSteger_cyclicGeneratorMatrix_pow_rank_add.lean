-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGeneratorMatrix_pow_rank_add
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicGeneratorMatrix_pow_rank_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:59:26.782399+00:00
-- url     : https://prove2.me/theorems/8edd1314-86a5-41c6-a902-932a2a75f317
-- title:
--   Cartwright Steger: cyclic Generator Matrix pow rank add
-- statement:
--   Crossing the finite cyclic basis boundary contributes the central
--   factor `1 + y`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L165-L170
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L165-L170

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicGeneratorMatrix_pow_rank_add
    (P : BasePrime) (r : Rank) (n : ℕ) :
    cyclicGeneratorMatrix P r ^ (r.matrixRank + n) =
      (onePlusY P r) • cyclicGeneratorMatrix P r ^ n := by sorry
