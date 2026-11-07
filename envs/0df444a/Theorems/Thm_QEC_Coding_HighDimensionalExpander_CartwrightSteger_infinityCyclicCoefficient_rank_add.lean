-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityCyclicCoefficient_rank_add
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityCyclicCoefficient_rank_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:59:35.092888+00:00
-- url     : https://prove2.me/theorems/66ce60a5-e1a4-48ca-badb-c4b8ac707b1f
-- title:
--   Cartwright Steger: infinity Cyclic Coefficient rank add
-- statement:
--   The inverse-expansion coefficients are periodic with period `d`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L241-L247
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L241-L247

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityCyclicCoefficient_rank_add
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) (n : ℕ) :
    infinityCyclicCoefficient P r u (r.matrixRank + n) =
      infinityCyclicCoefficient P r u n := by sorry
