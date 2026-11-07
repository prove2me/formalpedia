-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingIntegralUnitPGLHom_monomial
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingIntegralUnitPGLHom_monomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:33:27.085102+00:00
-- url     : https://prove2.me/theorems/f5af0a78-b160-4ac0-aaec-b4f191ea1f78
-- title:
--   Cartwright Steger: building Integral Unit PGLHom monomial
-- statement:
--   The Cartwright Steger construction uses the building Integral Unit PGLHom monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingSkewRepresentation.lean#L260-L275
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingSkewRepresentation.lean#L260-L275

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingCompactNormalForm
import Mathlib.Algebra.SkewMonoidAlgebra.Lift
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingSkewRepresentation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingIntegralUnitPGLHom_monomial
    (P : BasePrime) (r : Rank)
    (c : (ConstantExtension P r)ˣ) (n : ℤ) :
    buildingIntegralUnitPGLHom P r
        (skewLaurentMonomialUnit P r c n) =
      buildingConstantPGLHom P r c *
        buildingCyclicGeneratorPGL P r ^ n := by sorry
