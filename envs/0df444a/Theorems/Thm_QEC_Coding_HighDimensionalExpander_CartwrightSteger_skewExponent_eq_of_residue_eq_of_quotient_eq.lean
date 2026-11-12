-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewExponent_eq_of_residue_eq_of_quotient_eq
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewExponent_eq_of_residue_eq_of_quotient_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:20:01.918545+00:00
-- url     : https://prove2.me/theorems/c0c5310e-2fc7-41c8-b4b7-fef86dc5698b
-- title:
--   Cartwright Steger: skew Exponent eq of residue eq of quotient eq
-- statement:
--   The Cartwright Steger construction uses the skew Exponent eq of residue eq of quotient eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewResidueCoordinates.lean#L44-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewResidueCoordinates.lean#L44-L50

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_LaurentEvaluation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewResidueCoordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewExponent_eq_of_residue_eq_of_quotient_eq
    (r : Rank) {m n : ℤ}
    (hres : skewExponentResidue r m = skewExponentResidue r n)
    (hquot : skewExponentQuotient r m = skewExponentQuotient r n) :
    m = n := by sorry
