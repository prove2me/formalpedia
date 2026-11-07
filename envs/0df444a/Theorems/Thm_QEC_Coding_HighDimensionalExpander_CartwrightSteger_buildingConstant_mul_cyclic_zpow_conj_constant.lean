-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingConstant_mul_cyclic_zpow_conj_constant
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingConstant_mul_cyclic_zpow_conj_constant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:19:27.878177+00:00
-- url     : https://prove2.me/theorems/f6a2d66c-8255-483f-b3e8-6451e2435d21
-- title:
--   Cartwright Steger: building Constant mul cyclic zpow conj constant
-- statement:
--   Conjugation by a compact normal form `u z^n` only remembers the
--   cyclic exponent on the represented constant field.  The leading constant
--   factor disappears because the constant extension is commutative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L273-L301
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L273-L301

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingAction
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingConstant_mul_cyclic_zpow_conj_constant
    (P : BasePrime) (r : Rank) (u v : (ConstantExtension P r)ˣ) (n : ℤ) :
    (buildingConstantPGLHom P r u *
          buildingCyclicGeneratorPGL P r ^ n) *
        buildingConstantPGLHom P r v *
        (buildingConstantPGLHom P r u *
          buildingCyclicGeneratorPGL P r ^ n)⁻¹ =
      buildingConstantPGLHom P r
        ((constantFrobeniusUnitEquiv P r ^ n) v) := by sorry
