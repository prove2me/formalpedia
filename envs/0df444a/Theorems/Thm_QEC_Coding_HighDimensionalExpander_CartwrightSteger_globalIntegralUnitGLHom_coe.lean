-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_globalIntegralUnitGLHom_coe
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.globalIntegralUnitGLHom_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:00:30.200246+00:00
-- url     : https://prove2.me/theorems/88ca8ce6-127a-4ae3-9e06-ef93992e1162
-- title:
--   Cartwright Steger: global Integral Unit GLHom coe
-- statement:
--   The Cartwright Steger construction uses the global Integral Unit GLHom coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/ProjectiveUnits.lean#L24-L31
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/ProjectiveUnits.lean#L24-L31

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_ProjectiveUnits
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.globalIntegralUnitGLHom_coe
    (P : BasePrime) (r : Rank)
    (u : (CartwrightStegerSkewLaurentRing P r)ˣ) :
    (globalIntegralUnitGLHom P r u :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) =
      skewLaurentToGlobalMatrix P r u := by sorry

attribute [defeq] QEC.Coding.HighDimensionalExpander.CartwrightSteger.globalIntegralUnitGLHom_coe
