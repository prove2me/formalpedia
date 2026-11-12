-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewExponentResidue_val
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewExponentResidue_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:19:27.380004+00:00
-- url     : https://prove2.me/theorems/80570aa5-7801-4f15-b624-b360765accb1
-- title:
--   Cartwright Steger: skew Exponent Residue val
-- statement:
--   The Cartwright Steger construction uses the skew Exponent Residue val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewResidueCoordinates.lean#L25-L28
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewResidueCoordinates.lean#L25-L28

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_LaurentEvaluation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewResidueCoordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewExponentResidue_val
    (r : Rank) (n : ℤ) :
    ((skewExponentResidue r n : Fin r.matrixRank) : ℕ) =
      (n % (r.matrixRank : ℤ)).toNat := by sorry

attribute [defeq] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewExponentResidue_val
