-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingConstantPGL_eq_of_quotientMk_eq
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingConstantPGL_eq_of_quotientMk_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:05:12.914323+00:00
-- url     : https://prove2.me/theorems/be127ed0-d317-4ab2-8977-075ca2682e8f
-- title:
--   Cartwright Steger: building Constant PGL eq of quotient Mk eq
-- statement:
--   The Cartwright Steger construction uses the building Constant PGL eq of quotient Mk eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingConstantKernel.lean#L183-L195
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingConstantKernel.lean#L183-L195

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_CompactNormalForm
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingConstantKernel
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingConstantPGL_eq_of_quotientMk_eq
    (P : BasePrime) (r : Rank)
    (u v : (ConstantExtension P r)ˣ)
    (h : (QuotientGroup.mk u : ConstantProjectiveClass P r) =
      QuotientGroup.mk v) :
    buildingConstantPGLHom P r u = buildingConstantPGLHom P r v := by sorry
