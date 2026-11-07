-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantFrobenius_pow_rank_add_apply
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantFrobenius_pow_rank_add_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:02:20.688399+00:00
-- url     : https://prove2.me/theorems/93c9a58a-8550-4ef9-965e-ee19c247840b
-- title:
--   Cartwright Steger: constant Frobenius pow rank add apply
-- statement:
--   Frobenius powers are periodic with the cyclic-algebra degree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L233-L238
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L233-L238

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantFrobenius_pow_rank_add_apply
    (P : BasePrime) (r : Rank) (n : ℕ) (c : ConstantExtension P r) :
    (constantFrobenius P r ^ (r.matrixRank + n)) c =
      (constantFrobenius P r ^ n) c := by sorry
