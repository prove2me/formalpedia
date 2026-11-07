-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_globalIntegralUnitPGLHom_eq_constant_mul_zpow
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.globalIntegralUnitPGLHom_eq_constant_mul_zpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:00:28.311921+00:00
-- url     : https://prove2.me/theorems/516c7ff0-f078-4dcc-847b-19dc16adea56
-- title:
--   Cartwright Steger: global Integral Unit PGLHom eq constant mul zpow
-- statement:
--   The Cartwright Steger construction uses the global Integral Unit PGLHom eq constant mul zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/ProjectiveUnits.lean#L54-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/ProjectiveUnits.lean#L54-L74

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_ProjectiveUnits
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.globalIntegralUnitPGLHom_eq_constant_mul_zpow
    (P : BasePrime) (r : Rank)
    (u : (CartwrightStegerSkewLaurentRing P r)ˣ) :
    ∃ c : (ConstantExtension P r)ˣ, ∃ n : ℤ,
      globalIntegralUnitPGLHom P r u =
        globalConstantPGLHom P r c *
          globalCyclicGeneratorPGL P r ^ n := by sorry
