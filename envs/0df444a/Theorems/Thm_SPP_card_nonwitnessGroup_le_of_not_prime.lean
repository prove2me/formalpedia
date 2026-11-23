-- Prove2me | Theorems.Thm_SPP_card_nonwitnessGroup_le_of_not_prime
-- name    : SPP.card_nonwitnessGroup_le_of_not_prime
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T08:10:02.730178+00:00
-- url     : https://prove2.me/theorems/84d20237-4837-4fb3-90a0-c6ed7d9fa124
-- title:
--   SPP: card nonwitness Group le of not prime
-- statement:
--   The proportion of Miller–Rabin nonwitnesses of odd composite `n` in `(ZMod n)ˣ` is at most 1/4.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L622-L652
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L622-L652

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

theorem SPP.card_nonwitnessGroup_le_of_not_prime [Fact (1 < n)]
    (ho : Odd n) (hnp : ¬n.Prime) (h9 : n ≠ 9) :
    4 * Nat.card (nonwitnessGroup n) ≤ φ n := by sorry
