-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantConjugatedCartwrightStegerB_conj_monomial_preExpansion
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantConjugatedCartwrightStegerB_conj_monomial_preExpansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:03:30.684795+00:00
-- url     : https://prove2.me/theorems/023415fd-8054-4ec3-9b8f-f4b869640e5a
-- title:
--   Cartwright Steger: constant Conjugated Cartwright Steger B conj monomial pre Expansion
-- statement:
--   Exact conjugation before collecting equal cyclic powers.  Both
--   factors on the right have already been computed from the construction;
--   the remaining equation-(9) step is finite-sum reindexing and coefficient
--   collection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L701-L721
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L701-L721

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantConjugatedCartwrightStegerB_conj_monomial_preExpansion
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k : ℕ) (ζ : ConstantExtension P r) :
    ((constantConjugatedCartwrightStegerB P r u :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) *
        (constantMatrix P r ζ * cyclicGeneratorMatrix P r ^ k)) *
        (((constantConjugatedCartwrightStegerB P r u)⁻¹ :
            Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (SplittingFunctionField P r)) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) =
      (constantMatrix P r ζ * cyclicGeneratorMatrix P r ^ k -
        constantMatrix P r
          (infinityCyclicInverseCoefficient P r u *
            (constantFrobenius P r).symm ζ) *
          cyclicGeneratorInverseMatrix P r *
            cyclicGeneratorMatrix P r ^ k) *
        constantConjugatedBInverseExpansion P r u := by sorry
