-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_constant_zpow_of_skewLaurent_unit
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_constant_zpow_of_skewLaurent_unit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:53:33.228546+00:00
-- url     : https://prove2.me/theorems/fdd618c9-52a0-4ae6-b6d0-6dada158ecc8
-- title:
--   Cartwright Steger: exists constant zpow of skew Laurent unit
-- statement:
--   Every unit of the actual skew Laurent ring is a nonzero constant times
--   one integral power of `z`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewUnits.lean#L208-L273
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewUnits.lean#L208-L273

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewRing
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewUnits
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Multiplicative SkewMonoidAlgebra

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_constant_zpow_of_skewLaurent_unit
    (P : BasePrime) (r : Rank)
    (u : (CartwrightStegerSkewLaurentRing P r)ˣ) :
    ∃ c : (ConstantExtension P r)ˣ, ∃ n : ℤ,
      (u : CartwrightStegerSkewLaurentRing P r) =
        SkewMonoidAlgebra.single (Multiplicative.ofAdd n)
          (c : ConstantExtension P r) := by sorry
