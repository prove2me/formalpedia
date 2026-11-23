-- Prove2me | Theorems.Thm_SPP_nonwitnessGroup_lt_lt_of_not_isPrimePow
-- name    : SPP.nonwitnessGroup_lt_lt_of_not_isPrimePow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:10:09.743317+00:00
-- url     : https://prove2.me/theorems/802628b5-572e-438c-8fd5-1b20639d8a92
-- title:
--   SPP: nonwitness Group lt lt of not is Prime Pow
-- statement:
--   By combining the cases for Carmichael and non-Carmichael, we get the following lemma,
--   from which the Miller–Rabin property follows easily.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L594-L617
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L594-L617

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

theorem SPP.nonwitnessGroup_lt_lt_of_not_isPrimePow [Fact (1 < n)] (ho : Odd n) (hnpp : ¬IsPrimePow n) :
    ∃ K : Subgroup (ZMod n)ˣ, nonwitnessGroup n < K ∧ K < ⊤ := by sorry
