-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurent_support_max_mul
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurent_support_max_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:53:22.906689+00:00
-- url     : https://prove2.me/theorems/4c9ab5e2-7b54-433b-9d0f-47abe152605c
-- title:
--   Cartwright Steger: skew Laurent support max mul
-- statement:
--   The Cartwright Steger construction uses the skew Laurent support max mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewUnits.lean#L110-L134
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewUnits.lean#L110-L134

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewRing
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewUnits
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Multiplicative SkewMonoidAlgebra

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurent_support_max_mul
    (P : BasePrime) (r : Rank)
    {f g : CartwrightStegerSkewLaurentRing P r}
    {a b : ℤ}
    (ha : Multiplicative.ofAdd a ∈ f.support)
    (hmaxa : ∀ x, Multiplicative.ofAdd x ∈ f.support → x ≤ a)
    (hb : Multiplicative.ofAdd b ∈ g.support)
    (hmaxb : ∀ x, Multiplicative.ofAdd x ∈ g.support → x ≤ b) :
    Multiplicative.ofAdd (a + b) ∈ (f * g).support ∧
      ∀ x, Multiplicative.ofAdd x ∈ (f * g).support → x ≤ a + b := by sorry
