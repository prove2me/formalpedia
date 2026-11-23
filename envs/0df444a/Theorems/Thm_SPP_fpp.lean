-- Prove2me | Theorems.Thm_SPP_fpp
-- name    : SPP.fpp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:03:07.067784+00:00
-- url     : https://prove2.me/theorems/196911aa-0c1a-4cbe-9569-144dcf86e012
-- title:
--   SPP: fpp
-- statement:
--   Strong probable primes are Fermat probable primes.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L144-L150
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L144-L150

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

theorem SPP.fpp {n : ℕ} {a : ZMod n} (h : SPP n a) :
    FPP n a := by sorry
