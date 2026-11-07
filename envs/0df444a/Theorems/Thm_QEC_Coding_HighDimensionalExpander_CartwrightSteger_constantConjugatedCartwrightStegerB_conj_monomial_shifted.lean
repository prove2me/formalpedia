-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantConjugatedCartwrightStegerB_conj_monomial_shifted
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantConjugatedCartwrightStegerB_conj_monomial_shifted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:04:03.532603+00:00
-- url     : https://prove2.me/theorems/3e4cc490-790f-42f6-93ad-ecb38d9b7d59
-- title:
--   Cartwright Steger: constant Conjugated Cartwright Steger B conj monomial shifted
-- statement:
--   Before reducing cyclic exponents modulo `d`, conjugation is the leading
--   monomial plus `y⁻¹` times the shifted correction sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L1073-L1095
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L1073-L1095

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantConjugatedCartwrightStegerB_conj_monomial_shifted
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k : ℕ) (ζ : ConstantExtension P r) :
    ((constantConjugatedCartwrightStegerB P r u :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) *
        infinityLeadingMonomial P r k ζ) *
        (((constantConjugatedCartwrightStegerB P r u)⁻¹ :
            Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (SplittingFunctionField P r)) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) =
      infinityLeadingMonomial P r k ζ +
        (splittingY P r)⁻¹ •
          ∑ i ∈ Finset.range r.matrixRank,
            infinityShiftedCorrectionTerm P r u k i ζ := by sorry
