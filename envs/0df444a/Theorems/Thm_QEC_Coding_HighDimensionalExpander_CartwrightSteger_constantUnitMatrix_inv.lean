-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_inv
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:59:10.603191+00:00
-- url     : https://prove2.me/theorems/83caa16e-9d6e-4f29-87fd-bda65ca7c86b
-- title:
--   Cartwright Steger: constant Unit Matrix inv
-- statement:
--   The Cartwright Steger construction uses the constant Unit Matrix inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L29-L33
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L29-L33

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_inv
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    (constantUnitMatrix P r u)⁻¹ = constantUnitMatrix P r u⁻¹ := by sorry
