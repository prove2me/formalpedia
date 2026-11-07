-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantConjugatedCartwrightStegerB_conj_monomial
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantConjugatedCartwrightStegerB_conj_monomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:04:09.934207+00:00
-- url     : https://prove2.me/theorems/7afdcfe9-ad48-4922-8f4c-24c549f9351d
-- title:
--   Cartwright Steger: constant Conjugated Cartwright Steger B conj monomial
-- statement:
--   LSV05b equation (9), proved for every cyclic-basis exponent.  The sole
--   premise is the intrinsic basis bound `k ≤ d`; all displayed coefficients
--   are computed definitions rather than assumed data.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L1169-L1196
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L1169-L1196

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantConjugatedCartwrightStegerB_conj_monomial
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k : ℕ) (hk : k ≤ r.matrixRank) (ζ : ConstantExtension P r) :
    ((constantConjugatedCartwrightStegerB P r u :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) *
        (constantMatrix P r ζ * cyclicGeneratorMatrix P r ^ k)) *
        (((constantConjugatedCartwrightStegerB P r u)⁻¹ :
            Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (SplittingFunctionField P r)) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) =
      infinityConjugationFormula P r u k ζ := by sorry
