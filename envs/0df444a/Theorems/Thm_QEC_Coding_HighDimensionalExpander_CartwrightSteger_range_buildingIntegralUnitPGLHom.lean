-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_range_buildingIntegralUnitPGLHom
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.range_buildingIntegralUnitPGLHom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:33:42.796615+00:00
-- url     : https://prove2.me/theorems/5ee073de-3085-412f-8044-c5e669595eac
-- title:
--   Cartwright Steger: range building Integral Unit PGLHom
-- statement:
--   The Cartwright Steger construction uses the range building Integral Unit PGLHom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingSkewRepresentation.lean#L277-L307
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingSkewRepresentation.lean#L277-L307

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingCompactNormalForm
import Mathlib.Algebra.SkewMonoidAlgebra.Lift
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingSkewRepresentation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.range_buildingIntegralUnitPGLHom
    (P : BasePrime) (r : Rank) :
    (buildingIntegralUnitPGLHom P r).range =
      BuildingCompactCyclicSubgroup P r := by sorry
