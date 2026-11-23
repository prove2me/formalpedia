-- Prove2me | Theorems.Thm_SPP_card_le_of_not_prime
-- name    : SPP.card_le_of_not_prime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:10:33.709609+00:00
-- url     : https://prove2.me/theorems/02f27b57-79a1-4b97-a6b9-9e0adccb08e5
-- title:
--   SPP: card le of not prime
-- statement:
--   The proportion of Miller–Rabin nonwitnesses of odd composite `n` in `ZMod n \ {0}` is at most 1/4.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L661-L686
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L661-L686

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
open Finset

theorem SPP.card_le_of_not_prime {n : ℕ} [hn : Fact (1 < n)] (ho : Odd n) (hnp : ¬n.Prime) :
    4 * #{a | SPP n a} ≤ n - 1 := by sorry
