-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingCompactNormalForm_conj_constantCyclicMonomial
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingCompactNormalForm_conj_constantCyclicMonomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:19:40.081685+00:00
-- url     : https://prove2.me/theorems/d4c2c15c-41d5-42c5-8c4f-52ad2642a1f6
-- title:
--   Cartwright Steger: building Compact Normal Form conj constant Cyclic Monomial
-- statement:
--   The computed block formula agrees with actual projective inner
--   conjugation on every nonzero cyclic monomial.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L388-L437
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L388-L437

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingAction
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingCompactNormalForm_conj_constantCyclicMonomial
    (P : BasePrime) (r : Rank) (u v : (ConstantExtension P r)ˣ)
    (j k : ℕ) :
    (buildingConstantPGLHom P r u *
          buildingCyclicGeneratorPGL P r ^ j) *
        (buildingConstantPGLHom P r v *
          buildingCyclicGeneratorPGL P r ^ k) *
        (buildingConstantPGLHom P r u *
          buildingCyclicGeneratorPGL P r ^ j)⁻¹ =
      buildingConstantPGLHom P r
          (compactConjugationDiagonalUnit P r u v j k) *
        buildingCyclicGeneratorPGL P r ^ k := by sorry
