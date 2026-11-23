-- Prove2me | Theorems.Thm_SPP_nonwitnessGroup_le
-- name    : SPP.nonwitnessGroup_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:03:12.077715+00:00
-- url     : https://prove2.me/theorems/118149f2-85af-476e-bae8-694c93b93cc8
-- title:
--   SPP: nonwitness Group le
-- statement:
--   The SPP construction uses the nonwitness Group le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L176-L178
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L176-L178

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

theorem SPP.nonwitnessGroup_le (K : Subgroup (ZMod n)ˣ) (h : ∀ a : (ZMod n)ˣ, SPP n a → a ∈ K) :
    nonwitnessGroup n ≤ K := by sorry
