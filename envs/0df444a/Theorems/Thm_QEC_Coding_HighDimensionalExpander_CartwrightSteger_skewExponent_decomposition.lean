-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewExponent_decomposition
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewExponent_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:19:34.785977+00:00
-- url     : https://prove2.me/theorems/ceaf354d-8169-416b-837d-9660889eb9d1
-- title:
--   Cartwright Steger: skew Exponent decomposition
-- statement:
--   The Cartwright Steger construction uses the skew Exponent decomposition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewResidueCoordinates.lean#L30-L42
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewResidueCoordinates.lean#L30-L42

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_LaurentEvaluation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewResidueCoordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewExponent_decomposition
    (r : Rank) (n : ℤ) :
    n = (r.matrixRank : ℤ) * skewExponentQuotient r n +
      (skewExponentResidue r n : ℕ) := by sorry
