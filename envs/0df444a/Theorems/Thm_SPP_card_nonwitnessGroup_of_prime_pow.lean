-- Prove2me | Theorems.Thm_SPP_card_nonwitnessGroup_of_prime_pow
-- name    : SPP.card_nonwitnessGroup_of_prime_pow
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T08:07:05.729652+00:00
-- url     : https://prove2.me/theorems/8d3aa9dc-41b5-4796-8092-2a14a7d2fca5
-- title:
--   SPP: card nonwitness Group of prime pow
-- statement:
--   The SPP construction uses the card nonwitness Group of prime pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L361-L363
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L361-L363

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

theorem SPP.card_nonwitnessGroup_of_prime_pow (hm : 0 < m) (hp : 2 < p) :
    Nat.card (nonwitnessGroup (p ^ m)) = p - 1 := by sorry
