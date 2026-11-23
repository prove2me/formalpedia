-- Prove2me | Theorems.Thm_SPP_nonwitnessGroup_le_G
-- name    : SPP.nonwitnessGroup_le_G
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T08:07:56.434955+00:00
-- url     : https://prove2.me/theorems/1d62c4fd-c259-40ba-8fcf-7b99e7631091
-- title:
--   SPP: nonwitness Group le G
-- statement:
--   The SPP construction uses the nonwitness Group le G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L395-L406
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L395-L406

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

theorem SPP.nonwitnessGroup_le_G :
    nonwitnessGroup n ≤ G n := by sorry
