-- Prove2me | Theorems.Thm_P2M_two_pow_val__dvd_f36ca7a4dc65
-- name    : P2M_two_pow_val__dvd_f36ca7a4dc65
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:10:35.762081+00:00
-- url     : https://prove2.me/theorems/61510401-f1e0-4c1b-a559-e4ae229cd4e7
-- title:
--   P2 M two pow val  dvd f36ca7a4dc65: P2 M two pow val  dvd f36ca7a4dc65
-- statement:
--   The P2 M two pow val  dvd f36ca7a4dc65 construction uses the P2 M two pow val  dvd f36ca7a4dc65 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Val2.lean#L17-L18
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Val2.lean#L17-L18

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_MillerRabin_Val2
set_option autoImplicit false
open Nat

theorem P2M_two_pow_val__dvd_f36ca7a4dc65 (n : ℕ) : 2 ^ val₂ n ∣ n := by sorry

alias «two_pow_val₂_dvd» := P2M_two_pow_val__dvd_f36ca7a4dc65
