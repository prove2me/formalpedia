-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentMonomialUnit_val
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentMonomialUnit_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:50:58.987243+00:00
-- url     : https://prove2.me/theorems/276905c0-57ae-4927-867c-19e60d92a735
-- title:
--   Cartwright Steger: skew Laurent Monomial Unit val
-- statement:
--   The Cartwright Steger construction uses the skew Laurent Monomial Unit val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewRing.lean#L86-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewRing.lean#L86-L92

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Mathlib.Algebra.SkewMonoidAlgebra.Support
import Mathlib.Algebra.Ring.Action.End
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewRing
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentMonomialUnit_val
    (P : BasePrime) (r : Rank)
    (c : (ConstantExtension P r)ˣ) (n : ℤ) :
    (skewLaurentMonomialUnit P r c n :
      CartwrightStegerSkewLaurentRing P r) =
      SkewMonoidAlgebra.single (Multiplicative.ofAdd n)
        (c : ConstantExtension P r) := by sorry

attribute [defeq] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentMonomialUnit_val
