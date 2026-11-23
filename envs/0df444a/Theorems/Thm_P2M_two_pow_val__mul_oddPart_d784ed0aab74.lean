-- Prove2me | Theorems.Thm_P2M_two_pow_val__mul_oddPart_d784ed0aab74
-- name    : P2M_two_pow_val__mul_oddPart_d784ed0aab74
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:10:33.678137+00:00
-- url     : https://prove2.me/theorems/a6211c18-f89e-46ce-9938-1e2c140b257f
-- title:
--   P2 M two pow val  mul odd Part d784ed0aab74: P2 M two pow val  mul odd Part d784ed0aab74
-- statement:
--   The P2 M two pow val  mul odd Part d784ed0aab74 construction uses the P2 M two pow val  mul odd Part d784ed0aab74 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Val2.lean#L20-L21
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Val2.lean#L20-L21

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_MillerRabin_Val2
set_option autoImplicit false
open Nat

theorem P2M_two_pow_val__mul_oddPart_d784ed0aab74 (n : ℕ) : 2 ^ val₂ n * oddPart n = n := by sorry

alias «two_pow_val₂_mul_oddPart» := P2M_two_pow_val__mul_oddPart_d784ed0aab74
