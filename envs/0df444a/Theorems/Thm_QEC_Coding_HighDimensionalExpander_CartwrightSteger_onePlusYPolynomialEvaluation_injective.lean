-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_onePlusYPolynomialEvaluation_injective
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.onePlusYPolynomialEvaluation_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:16:45.835792+00:00
-- url     : https://prove2.me/theorems/88027d68-db11-4362-b9eb-b41e048caf03
-- title:
--   Cartwright Steger: one Plus YPolynomial Evaluation injective
-- statement:
--   The Cartwright Steger construction uses the one Plus YPolynomial Evaluation injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/LaurentEvaluation.lean#L48-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/LaurentEvaluation.lean#L48-L73

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewReconstructionTheorem
import Mathlib.Algebra.Polynomial.Laurent
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_LaurentEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.onePlusYPolynomialEvaluation_injective
    (P : BasePrime) (r : Rank) :
    Function.Injective
      (fun f : Polynomial (ConstantExtension P r) =>
        Polynomial.eval₂
          (algebraMap (ConstantExtension P r) (SplittingFunctionField P r))
          (onePlusY P r) f) := by sorry
