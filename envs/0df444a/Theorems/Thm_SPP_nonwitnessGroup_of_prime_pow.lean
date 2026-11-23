-- Prove2me | Theorems.Thm_SPP_nonwitnessGroup_of_prime_pow
-- name    : SPP.nonwitnessGroup_of_prime_pow
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T08:06:40.722707+00:00
-- url     : https://prove2.me/theorems/2a5a62ae-bccc-4ab4-ae82-d18def740e03
-- title:
--   SPP: nonwitness Group of prime pow
-- statement:
--   The SPP construction uses the nonwitness Group of prime pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L226-L255
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L226-L255

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
variable {m p : ℕ} [pp : Fact p.Prime]

theorem SPP.nonwitnessGroup_of_prime_pow (hm : 0 < m) (hp : 2 < p) :
    nonwitnessGroup (p ^ m) = (powMonoidHom (p - 1)).ker := by sorry
