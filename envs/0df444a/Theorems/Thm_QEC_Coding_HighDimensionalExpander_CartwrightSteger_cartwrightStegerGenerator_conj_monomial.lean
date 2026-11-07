-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGenerator_conj_monomial
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerGenerator_conj_monomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:59:15.956201+00:00
-- url     : https://prove2.me/theorems/1bad334e-529c-4e6d-93af-e60bfd69fa2a
-- title:
--   Cartwright Steger: cartwright Steger Generator conj monomial
-- statement:
--   Equation (9) for every actual class-indexed generator owned by the
--   Cartwright--Steger matrix group.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L1200-L1217
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L1200-L1217

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerGenerator_conj_monomial
    (P : BasePrime) (r : Rank) (x : ConstantProjectiveClass P r)
    (k : Fin r.matrixRank) (ζ : ConstantExtension P r) :
    ((cartwrightStegerGenerator P r x :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) *
        (constantMatrix P r ζ * cyclicGeneratorMatrix P r ^ (k : ℕ))) *
        (((cartwrightStegerGenerator P r x)⁻¹ :
            Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (SplittingFunctionField P r)) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) =
      infinityConjugationFormula P r
        (constantClassRepresentative P r x) (k : ℕ) ζ := by sorry
