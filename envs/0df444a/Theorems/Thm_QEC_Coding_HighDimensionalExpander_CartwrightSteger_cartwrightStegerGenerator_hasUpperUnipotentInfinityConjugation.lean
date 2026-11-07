-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGenerator_hasUpperUnipotentInfinityConjugation
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerGenerator_hasUpperUnipotentInfinityConjugation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:21:32.733254+00:00
-- url     : https://prove2.me/theorems/aeac0671-a350-42a7-9818-5af287398b2a
-- title:
--   Cartwright Steger: cartwright Steger Generator has Upper Unipotent Infinity Conjugation
-- statement:
--   Every construction-owned Cartwright--Steger generator satisfies the
--   upper-unipotent infinity condition, with the coefficients computed by
--   equation (9).
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L1247-L1259
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L1247-L1259

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerGenerator_hasUpperUnipotentInfinityConjugation
    (P : BasePrime) (r : Rank) (x : ConstantProjectiveClass P r) :
    HasUpperUnipotentInfinityConjugation P r
      (cartwrightStegerGenerator P r x) := by sorry
