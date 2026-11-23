-- Prove2me | Theorems.Thm_P2M_val__of_even_abec3e74f714
-- name    : P2M_val__of_even_abec3e74f714
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:10:37.140386+00:00
-- url     : https://prove2.me/theorems/785af7e3-2521-4a23-9c75-6e551b13d6ef
-- title:
--   P2 M val  of even abec3e74f714: P2 M val  of even abec3e74f714
-- statement:
--   The P2 M val  of even abec3e74f714 construction uses the P2 M val  of even abec3e74f714 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Val2.lean#L28-L29
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Val2.lean#L28-L29

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_MillerRabin_Val2
set_option autoImplicit false
open Nat
variable {n : ℕ}

theorem P2M_val__of_even_abec3e74f714 [hn : NeZero n] (h : Even n) : 0 < val₂ n := by sorry

alias «val₂_of_even» := P2M_val__of_even_abec3e74f714
