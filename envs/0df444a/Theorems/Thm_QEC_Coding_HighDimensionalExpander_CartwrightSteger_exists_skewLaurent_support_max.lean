-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_skewLaurent_support_max
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_skewLaurent_support_max
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:53:23.848551+00:00
-- url     : https://prove2.me/theorems/26283cc8-1018-4e51-accd-3fc1f239c2eb
-- title:
--   Cartwright Steger: exists skew Laurent support max
-- statement:
--   The Cartwright Steger construction uses the exists skew Laurent support max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewUnits.lean#L40-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewUnits.lean#L40-L51

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewRing
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewUnits
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Multiplicative SkewMonoidAlgebra

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_skewLaurent_support_max
    (P : BasePrime) (r : Rank)
    {f : CartwrightStegerSkewLaurentRing P r} (hf : f ≠ 0) :
    ∃ a : ℤ, Multiplicative.ofAdd a ∈ f.support ∧
      ∀ x, Multiplicative.ofAdd x ∈ f.support → x ≤ a := by sorry
