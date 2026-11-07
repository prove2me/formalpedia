-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurent_support_min_mul
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurent_support_min_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:53:22.737785+00:00
-- url     : https://prove2.me/theorems/2ccf7a2b-d1d4-4bb6-a2fb-22cfef2a170f
-- title:
--   Cartwright Steger: skew Laurent support min mul
-- statement:
--   The Cartwright Steger construction uses the skew Laurent support min mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewUnits.lean#L180-L204
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewUnits.lean#L180-L204

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewRing
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewUnits
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Multiplicative SkewMonoidAlgebra

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurent_support_min_mul
    (P : BasePrime) (r : Rank)
    {f g : CartwrightStegerSkewLaurentRing P r}
    {a b : ℤ}
    (ha : Multiplicative.ofAdd a ∈ f.support)
    (hmina : ∀ x, Multiplicative.ofAdd x ∈ f.support → a ≤ x)
    (hb : Multiplicative.ofAdd b ∈ g.support)
    (hminb : ∀ x, Multiplicative.ofAdd x ∈ g.support → b ≤ x) :
    Multiplicative.ofAdd (a + b) ∈ (f * g).support ∧
      ∀ x, Multiplicative.ofAdd x ∈ (f * g).support → a + b ≤ x := by sorry
