-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_skewLaurentIntSupport
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_skewLaurentIntSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:52:02.183215+00:00
-- url     : https://prove2.me/theorems/f47c6e81-c267-4e6d-a295-9ddd4b7974b4
-- title:
--   Cartwright Steger: mem skew Laurent Int Support
-- statement:
--   The Cartwright Steger construction uses the mem skew Laurent Int Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewUnits.lean#L22-L27
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewUnits.lean#L22-L27

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewRing
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewUnits
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Multiplicative SkewMonoidAlgebra

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_skewLaurentIntSupport
    (P : BasePrime) (r : Rank)
    (f : CartwrightStegerSkewLaurentRing P r) (n : ℤ) :
    n ∈ skewLaurentIntSupport P r f ↔
      Multiplicative.ofAdd n ∈ f.support := by sorry
