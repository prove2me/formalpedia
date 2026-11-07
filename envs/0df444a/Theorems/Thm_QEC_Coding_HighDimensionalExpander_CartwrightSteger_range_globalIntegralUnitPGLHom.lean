-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_range_globalIntegralUnitPGLHom
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.range_globalIntegralUnitPGLHom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:00:26.092186+00:00
-- url     : https://prove2.me/theorems/182fa5d3-3480-494b-92c1-752998603abb
-- title:
--   Cartwright Steger: range global Integral Unit PGLHom
-- statement:
--   The Cartwright Steger construction uses the range global Integral Unit PGLHom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/ProjectiveUnits.lean#L102-L126
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/ProjectiveUnits.lean#L102-L126

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_ProjectiveUnits
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.range_globalIntegralUnitPGLHom
    (P : BasePrime) (r : Rank) :
    (globalIntegralUnitPGLHom P r).range =
      GlobalIntegralCompactCyclicSubgroup P r := by sorry
