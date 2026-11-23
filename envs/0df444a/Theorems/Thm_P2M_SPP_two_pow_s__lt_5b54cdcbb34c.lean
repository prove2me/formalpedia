-- Prove2me | Theorems.Thm_P2M_SPP_two_pow_s__lt_5b54cdcbb34c
-- name    : P2M_SPP_two_pow_s__lt_5b54cdcbb34c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:12:18.622081+00:00
-- url     : https://prove2.me/theorems/58141e09-c6a4-4dbf-8212-13f71f670cc6
-- title:
--   P2 M SPP two pow s  lt 5b54cdcbb34c: P2 M SPP two pow s  lt 5b54cdcbb34c
-- statement:
--   The P2 M SPP two pow s  lt 5b54cdcbb34c construction uses the P2 M SPP two pow s  lt 5b54cdcbb34c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L381-L386
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L381-L386

import Mathlib
import Definitions.Def_MillerRabin_Mathlib_Data_Fintype_Units
import Definitions.Def_MillerRabin_Mathlib_Algebra_Group_Subgroup_Lattice
import Definitions.Def_MillerRabin_FermatProbable
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Val2
import Definitions.Def_MillerRabin_StrongProbable
set_option autoImplicit false
open Nat
open SPP
open Subgroup
variable {n : ℕ}

theorem P2M_SPP_two_pow_s__lt_5b54cdcbb34c [Fact (1 < n)] (ho : Odd n) : 2 ^ s₀ n * oddPart (n - 1) < n - 1 := by sorry

alias «SPP».«two_pow_s₀_lt» := P2M_SPP_two_pow_s__lt_5b54cdcbb34c
