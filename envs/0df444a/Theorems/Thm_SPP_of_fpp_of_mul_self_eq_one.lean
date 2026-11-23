-- Prove2me | Theorems.Thm_SPP_of_fpp_of_mul_self_eq_one
-- name    : SPP.of_fpp_of_mul_self_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:03:31.004797+00:00
-- url     : https://prove2.me/theorems/27bff6cb-c921-4a94-b83d-8133b8624e21
-- title:
--   SPP: of fpp of mul self eq one
-- statement:
--   `n` is SPP to base `a` if `n` is FPP to base `a` and the square roots of 1 are ±1.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L121-L136
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L121-L136

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

theorem SPP.of_fpp_of_mul_self_eq_one {n : ℕ} {a : ZMod n}
    (hf : FPP n a) (h : ∀ x : ZMod n, x * x = 1 → x = 1 ∨ x = -1) :
    SPP n a := by sorry
