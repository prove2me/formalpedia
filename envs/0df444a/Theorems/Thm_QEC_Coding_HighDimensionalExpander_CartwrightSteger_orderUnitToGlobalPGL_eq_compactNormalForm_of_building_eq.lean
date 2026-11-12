-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderUnitToGlobalPGL_eq_compactNormalForm_of_building_eq
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderUnitToGlobalPGL_eq_compactNormalForm_of_building_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:45:10.434235+00:00
-- url     : https://prove2.me/theorems/a86e7997-8e20-4e0a-9434-f9a18aa39503
-- title:
--   Cartwright Steger: order Unit To Global PGL eq compact Normal Form of building eq
-- statement:
--   A projectively compact order unit and any compact normal form for its
--   building image determine the same global projective element.  The bridge is
--   an actual unit of the integral skew Laurent order, reconstructed together
--   with its inverse; no local-to-global injectivity is assumed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/SimpleTransitivity.lean#L113-L186
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/SimpleTransitivity.lean#L113-L186

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Stabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_SimpleTransitivity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderUnitToGlobalPGL_eq_compactNormalForm_of_building_eq
    (P : BasePrime) (r : Rank)
    (u : (CartwrightStegerOrder P r)ˣ)
    (hcompact : orderUnitToBuildingPGL P r u ∈
      SphericalHecke.maximalCompact (BaseField P) r.matrixRank)
    (c : (ConstantExtension P r)ˣ) (j : ℕ)
    (hbuilding : orderUnitToBuildingPGL P r u =
      buildingConstantPGLHom P r c *
        buildingCyclicGeneratorPGL P r ^ j) :
    orderUnitToGlobalPGL P r u =
      Matrix.ProjGenLinGroup.mk (globalCompactNormalForm P r c j) := by sorry
