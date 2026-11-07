-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantConjugatedCartwrightStegerB_inv
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantConjugatedCartwrightStegerB_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:03:14.783275+00:00
-- url     : https://prove2.me/theorems/fc433afc-5681-4d8c-922a-fb7e3630e4b8
-- title:
--   Cartwright Steger: constant Conjugated Cartwright Steger B inv
-- statement:
--   Inverting the conjugated generator preserves the outer constant
--   conjugation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L578-L585
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L578-L585

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantConjugatedCartwrightStegerB_inv
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    (constantConjugatedCartwrightStegerB P r u)⁻¹ =
      constantUnitMatrix P r u * (cartwrightStegerB P r)⁻¹ *
        constantUnitMatrix P r u⁻¹ := by sorry
