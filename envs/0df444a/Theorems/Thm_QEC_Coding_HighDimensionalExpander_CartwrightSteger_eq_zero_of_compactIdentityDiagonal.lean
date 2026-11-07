-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_eq_zero_of_compactIdentityDiagonal
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.eq_zero_of_compactIdentityDiagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:01:34.340485+00:00
-- url     : https://prove2.me/theorems/68ccb6be-f64c-4215-8403-7de3c81fe285
-- title:
--   Cartwright Steger: eq zero of compact Identity Diagonal
-- statement:
--   In the canonical exponent range, the infinity identity blocks force
--   the compact cyclic exponent itself to vanish.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L538-L544
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L538-L544

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingAction
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.eq_zero_of_compactIdentityDiagonal
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) (j : ℕ)
    (hj : j < r.matrixRank)
    (hdiag : CompactNormalFormHasIdentityDiagonal P r u j) :
    j = 0 := by sorry
