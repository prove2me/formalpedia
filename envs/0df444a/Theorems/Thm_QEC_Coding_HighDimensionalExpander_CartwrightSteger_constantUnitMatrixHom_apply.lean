-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrixHom_apply
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrixHom_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:58:42.608291+00:00
-- url     : https://prove2.me/theorems/db167d9c-39a0-4971-9db6-8b51b8aed15f
-- title:
--   Cartwright Steger: constant Unit Matrix Hom apply
-- statement:
--   The Cartwright Steger construction uses the constant Unit Matrix Hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L24-L27
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L24-L27

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrixHom_apply
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    constantUnitMatrixHom P r u = constantUnitMatrix P r u := by sorry

attribute [defeq] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrixHom_apply
