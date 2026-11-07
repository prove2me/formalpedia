-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_skewLaurent_support_min
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_skewLaurent_support_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:53:25.703092+00:00
-- url     : https://prove2.me/theorems/3612c9c7-e68a-4b46-8a65-f01d6795ba1a
-- title:
--   Cartwright Steger: exists skew Laurent support min
-- statement:
--   The Cartwright Steger construction uses the exists skew Laurent support min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewUnits.lean#L53-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewUnits.lean#L53-L64

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewRing
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewUnits
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Multiplicative SkewMonoidAlgebra

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_skewLaurent_support_min
    (P : BasePrime) (r : Rank)
    {f : CartwrightStegerSkewLaurentRing P r} (hf : f ≠ 0) :
    ∃ a : ℤ, Multiplicative.ofAdd a ∈ f.support ∧
      ∀ x, Multiplicative.ofAdd x ∈ f.support → a ≤ x := by sorry
