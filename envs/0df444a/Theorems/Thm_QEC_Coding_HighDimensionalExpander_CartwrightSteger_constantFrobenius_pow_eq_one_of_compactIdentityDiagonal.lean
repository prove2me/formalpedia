-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantFrobenius_pow_eq_one_of_compactIdentityDiagonal
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantFrobenius_pow_eq_one_of_compactIdentityDiagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:01:07.242128+00:00
-- url     : https://prove2.me/theorems/44954cf7-a60b-413e-b7b1-5280215f68a1
-- title:
--   Cartwright Steger: constant Frobenius pow eq one of compact Identity Diagonal
-- statement:
--   The zeroth identity block forces the cyclic exponent to act by the
--   identity Frobenius power.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L522-L534
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L522-L534

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingAction
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantFrobenius_pow_eq_one_of_compactIdentityDiagonal
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) (j : ℕ)
    (hdiag : CompactNormalFormHasIdentityDiagonal P r u j) :
    constantFrobenius P r ^ j = 1 := by sorry
