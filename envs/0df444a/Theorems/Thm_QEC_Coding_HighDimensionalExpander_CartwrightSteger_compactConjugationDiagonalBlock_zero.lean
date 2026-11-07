-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_compactConjugationDiagonalBlock_zero
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.compactConjugationDiagonalBlock_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:00:48.116338+00:00
-- url     : https://prove2.me/theorems/6f5c121d-81b8-4672-8c3b-64d19c8adc04
-- title:
--   Cartwright Steger: compact Conjugation Diagonal Block zero
-- statement:
--   On the zeroth cyclic block, compact inner conjugation is exactly the
--   Frobenius power contributed by `z^j`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L495-L509
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L495-L509

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingAction
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.compactConjugationDiagonalBlock_zero
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) (j : ℕ) :
    compactConjugationDiagonalBlock P r u j 0 =
      (constantFrobenius P r ^ j :
        ConstantExtension P r ≃ₐ[BaseField P] ConstantExtension P r).toLinearEquiv.toLinearMap := by sorry
