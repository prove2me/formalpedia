-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurent_coeff_mul_at_support_min_ne_zero
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurent_coeff_mul_at_support_min_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:53:31.600956+00:00
-- url     : https://prove2.me/theorems/498d2560-b0cf-40d0-b82e-e8236f4a8d02
-- title:
--   Cartwright Steger: skew Laurent coeff mul at support min ne zero
-- statement:
--   The Cartwright Steger construction uses the skew Laurent coeff mul at support min ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewUnits.lean#L136-L178
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewUnits.lean#L136-L178

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewRing
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewUnits
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Multiplicative SkewMonoidAlgebra

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurent_coeff_mul_at_support_min_ne_zero
    (P : BasePrime) (r : Rank)
    {f g : CartwrightStegerSkewLaurentRing P r}
    {a b : ℤ}
    (ha : Multiplicative.ofAdd a ∈ f.support)
    (hmina : ∀ x, Multiplicative.ofAdd x ∈ f.support → a ≤ x)
    (hb : Multiplicative.ofAdd b ∈ g.support)
    (hminb : ∀ x, Multiplicative.ofAdd x ∈ g.support → b ≤ x) :
    (f * g).coeff (Multiplicative.ofAdd (a + b)) ≠ 0 := by sorry
