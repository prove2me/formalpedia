-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_globalIntegralUnitPGLHom_monomial
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.globalIntegralUnitPGLHom_monomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:00:28.328684+00:00
-- url     : https://prove2.me/theorems/ee1b2f3b-51fa-4240-ae68-6ac3a8f3ae9f
-- title:
--   Cartwright Steger: global Integral Unit PGLHom monomial
-- statement:
--   The Cartwright Steger construction uses the global Integral Unit PGLHom monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/ProjectiveUnits.lean#L76-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/ProjectiveUnits.lean#L76-L92

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_ProjectiveUnits
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.globalIntegralUnitPGLHom_monomial
    (P : BasePrime) (r : Rank)
    (c : (ConstantExtension P r)ˣ) (n : ℤ) :
    globalIntegralUnitPGLHom P r (skewLaurentMonomialUnit P r c n) =
      globalConstantPGLHom P r c *
        globalCyclicGeneratorPGL P r ^ n := by sorry
