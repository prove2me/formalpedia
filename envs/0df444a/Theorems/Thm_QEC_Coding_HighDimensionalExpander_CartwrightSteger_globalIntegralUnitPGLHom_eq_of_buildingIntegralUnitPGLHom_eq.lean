-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_globalIntegralUnitPGLHom_eq_of_buildingIntegralUnitPGLHom_eq
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.globalIntegralUnitPGLHom_eq_of_buildingIntegralUnitPGLHom_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:45:39.678609+00:00
-- url     : https://prove2.me/theorems/c85c9e77-bcc7-4d25-9dd9-ccb91ce15c6f
-- title:
--   Cartwright Steger: global Integral Unit PGLHom eq of building Integral Unit PGLHom eq
-- statement:
--   Equality in the building projective representation transfers to equality
--   in the global projective representation because the two explicitly
--   constructed representations have the same proved kernel.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/Stabilizer.lean#L329-L343
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/Stabilizer.lean#L329-L343

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_LatticeBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_RepresentationKernel
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Stabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.globalIntegralUnitPGLHom_eq_of_buildingIntegralUnitPGLHom_eq
    (P : BasePrime) (r : Rank)
    {v w : (CartwrightStegerSkewLaurentRing P r)ˣ}
    (h : buildingIntegralUnitPGLHom P r v =
      buildingIntegralUnitPGLHom P r w) :
    globalIntegralUnitPGLHom P r v =
      globalIntegralUnitPGLHom P r w := by sorry
