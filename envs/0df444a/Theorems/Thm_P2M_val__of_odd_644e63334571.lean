-- Prove2me | Theorems.Thm_P2M_val__of_odd_644e63334571
-- name    : P2M_val__of_odd_644e63334571
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:13:12.338815+00:00
-- url     : https://prove2.me/theorems/60379fb7-a127-465c-8577-afe5806382c5
-- title:
--   P2 M val  of odd 644e63334571: P2 M val  of odd 644e63334571
-- statement:
--   The P2 M val  of odd 644e63334571 construction uses the P2 M val  of odd 644e63334571 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Val2.lean#L25-L26
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Val2.lean#L25-L26

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_MillerRabin_Val2
set_option autoImplicit false
open Nat
variable {n : ℕ}

theorem P2M_val__of_odd_644e63334571 (h : Odd n) : val₂ n = 0 := by sorry

alias «val₂_of_odd» := P2M_val__of_odd_644e63334571
