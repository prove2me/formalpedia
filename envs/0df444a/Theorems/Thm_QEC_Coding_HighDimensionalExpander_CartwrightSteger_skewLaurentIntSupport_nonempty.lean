-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentIntSupport_nonempty
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentIntSupport_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:51:55.916943+00:00
-- url     : https://prove2.me/theorems/1dfdcfaf-ebf9-4eec-8841-6e8b5dd20bdc
-- title:
--   Cartwright Steger: skew Laurent Int Support nonempty
-- statement:
--   The Cartwright Steger construction uses the skew Laurent Int Support nonempty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewUnits.lean#L29-L38
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewUnits.lean#L29-L38

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewRing
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewUnits
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Multiplicative SkewMonoidAlgebra

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentIntSupport_nonempty
    (P : BasePrime) (r : Rank)
    {f : CartwrightStegerSkewLaurentRing P r} (hf : f ≠ 0) :
    (skewLaurentIntSupport P r f).Nonempty := by sorry
