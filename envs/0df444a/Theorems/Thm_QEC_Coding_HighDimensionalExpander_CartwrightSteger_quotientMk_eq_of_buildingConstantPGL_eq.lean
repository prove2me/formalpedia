-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_quotientMk_eq_of_buildingConstantPGL_eq
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.quotientMk_eq_of_buildingConstantPGL_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:05:39.079802+00:00
-- url     : https://prove2.me/theorems/bcf2ad77-2f13-4176-b663-cceda147b956
-- title:
--   Cartwright Steger: quotient Mk eq of building Constant PGL eq
-- statement:
--   The Cartwright Steger construction uses the quotient Mk eq of building Constant PGL eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingConstantKernel.lean#L52-L181
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingConstantKernel.lean#L52-L181

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_CompactNormalForm
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingConstantKernel
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
set_option maxHeartbeats 400000

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.quotientMk_eq_of_buildingConstantPGL_eq
    (P : BasePrime) (r : Rank)
    (u v : (ConstantExtension P r)ˣ)
    (h : buildingConstantPGLHom P r u = buildingConstantPGLHom P r v) :
    (QuotientGroup.mk u : ConstantProjectiveClass P r) =
      QuotientGroup.mk v := by sorry
