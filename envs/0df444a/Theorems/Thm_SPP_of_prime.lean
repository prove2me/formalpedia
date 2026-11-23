-- Prove2me | Theorems.Thm_SPP_of_prime
-- name    : SPP.of_prime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:11:36.156657+00:00
-- url     : https://prove2.me/theorems/5cc10076-47f5-4bff-a143-1f0a1f87df69
-- title:
--   SPP: of prime
-- statement:
--   A prime is a strong probable prime to any nonzero base.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L139-L141
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L139-L141

import Mathlib
import Definitions.Def_MillerRabin_Mathlib_Data_Fintype_Units
import Definitions.Def_MillerRabin_Mathlib_Algebra_Group_Subgroup_Lattice
import Definitions.Def_MillerRabin_FermatProbable
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Val2
import Definitions.Def_MillerRabin_StrongProbable
import Theorems.Thm_FPP_of_prime

set_option autoImplicit false
open Nat
open SPP

theorem SPP.of_prime {p : ℕ} [Fact p.Prime] {a : ZMod p} (ha : a ≠ 0) :
    SPP p a := by sorry
