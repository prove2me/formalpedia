-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_compactConjugationDiagonalUnit_coe
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.compactConjugationDiagonalUnit_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:19:35.902806+00:00
-- url     : https://prove2.me/theorems/151695f0-9a88-4a64-b7b3-cc72ceee2235
-- title:
--   Cartwright Steger: compact Conjugation Diagonal Unit coe
-- statement:
--   The unit coefficient used in the monomial conjugation theorem is
--   exactly evaluation of the linear diagonal block.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L476-L491
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L476-L491

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingAction
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.compactConjugationDiagonalUnit_coe
    (P : BasePrime) (r : Rank) (u v : (ConstantExtension P r)ˣ)
    (j k : ℕ) :
    (compactConjugationDiagonalUnit P r u v j k : ConstantExtension P r) =
      compactConjugationDiagonalBlock P r u j k
        (v : ConstantExtension P r) := by sorry
