-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingConstant_mul_cyclic_pow_eq_one_of_compactIdentityDiagonal
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingConstant_mul_cyclic_pow_eq_one_of_compactIdentityDiagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:01:42.148755+00:00
-- url     : https://prove2.me/theorems/18a13855-0aa4-42d6-b8f7-99f587d7385f
-- title:
--   Cartwright Steger: building Constant mul cyclic pow eq one of compact Identity Diagonal
-- statement:
--   The complete compact obstruction: a normal form in the canonical
--   exponent range whose infinity conjugation has identity diagonal blocks is
--   the projective identity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L571-L582
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L571-L582

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingAction
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingConstant_mul_cyclic_pow_eq_one_of_compactIdentityDiagonal
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) (j : ℕ)
    (hj : j < r.matrixRank)
    (hdiag : CompactNormalFormHasIdentityDiagonal P r u j) :
    buildingConstantPGLHom P r u *
        buildingCyclicGeneratorPGL P r ^ j = 1 := by sorry
