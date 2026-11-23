-- Prove2me | Theorems.Thm_SPP_F_lt_top_of_not_carmichael
-- name    : SPP.F_lt_top_of_not_carmichael
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T08:09:37.906481+00:00
-- url     : https://prove2.me/theorems/786e37b2-b1e8-4519-9599-31ddf0dd9c1a
-- title:
--   SPP: F lt top of not carmichael
-- statement:
--   The SPP construction uses the F lt top of not carmichael property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L454-L458
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L454-L458

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

theorem SPP.F_lt_top_of_not_carmichael (hc : ¬FPP.Carmichael n): F n < ⊤ := by sorry
