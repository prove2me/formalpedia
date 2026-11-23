-- Prove2me | Theorems.Thm_SPP_mem_nonwitnessGroup
-- name    : SPP.mem_nonwitnessGroup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:03:11.801374+00:00
-- url     : https://prove2.me/theorems/4aa28ad3-a1d1-4386-b159-7876cc949524
-- title:
--   SPP: mem nonwitness Group
-- statement:
--   The SPP construction uses the mem nonwitness Group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L172-L174
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L172-L174

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

theorem SPP.mem_nonwitnessGroup {a : (ZMod n)ˣ} (h : SPP n a) :
    a ∈ nonwitnessGroup n := by sorry
