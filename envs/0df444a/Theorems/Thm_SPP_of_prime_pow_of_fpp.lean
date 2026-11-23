-- Prove2me | Theorems.Thm_SPP_of_prime_pow_of_fpp
-- name    : SPP.of_prime_pow_of_fpp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:06:57.919115+00:00
-- url     : https://prove2.me/theorems/b37a3976-d2dc-4ac3-8c44-cfab4a92a326
-- title:
--   SPP: of prime pow of fpp
-- statement:
--   The SPP construction uses the of prime pow of fpp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L187-L217
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L187-L217

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

theorem SPP.of_prime_pow_of_fpp {p m : ℕ} {a : ZMod (p ^ m)} [pp : Fact p.Prime]
    (hm : 0 < m) (hp : 2 < p) (ha : FPP (p ^ m) a) :
    SPP (p ^ m) a := by sorry
