-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantConjugatedCartwrightStegerB_conj_monomial_split
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantConjugatedCartwrightStegerB_conj_monomial_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:03:41.016973+00:00
-- url     : https://prove2.me/theorems/3331c985-172e-416f-89bd-ac1c660ab907
-- title:
--   Cartwright Steger: constant Conjugated Cartwright Steger B conj monomial split
-- statement:
--   Separate the exact conjugation into its non-`1/y` part and its
--   explicit `1/y` tail.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L744-L766
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L744-L766

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantConjugatedCartwrightStegerB_conj_monomial_split
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
      infinityLeadingMonomial P r k ζ -
          infinityDefectMonomial P r u k ζ +
        (splittingY P r)⁻¹ •
          (infinityLeadingMonomial P r k ζ *
              constantConjugatedBInverseTail P r u -
            infinityDefectMonomial P r u k ζ *
              constantConjugatedBInverseTail P r u) := by sorry
