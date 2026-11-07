-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantFrobeniusUnitEquiv_eq_of_compactIdentityDiagonal
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantFrobeniusUnitEquiv_eq_of_compactIdentityDiagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:01:46.374971+00:00
-- url     : https://prove2.me/theorems/52579c56-96b6-475c-ac38-8cd47db01666
-- title:
--   Cartwright Steger: constant Frobenius Unit Equiv eq of compact Identity Diagonal
-- statement:
--   After the cyclic exponent vanishes, the first identity block forces
--   the leading constant unit to be Frobenius-fixed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L548-L566
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L548-L566

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingAction
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantFrobeniusUnitEquiv_eq_of_compactIdentityDiagonal
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) (j : ℕ)
    (hj : j = 0)
    (hdiag : CompactNormalFormHasIdentityDiagonal P r u j) :
    constantFrobeniusUnitEquiv P r u = u := by sorry
