-- Prove2me | Theorems.Thm_SPP_orderOf_dvd_sub_one
-- name    : SPP.orderOf_dvd_sub_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:06:33.971881+00:00
-- url     : https://prove2.me/theorems/b5027d05-4b62-4b19-9930-3927467ca264
-- title:
--   SPP: order Of dvd sub one
-- statement:
--   The SPP construction uses the order Of dvd sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L152-L154
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L152-L154

import Mathlib
import Definitions.Def_MillerRabin_Mathlib_Data_Fintype_Units
import Definitions.Def_MillerRabin_Mathlib_Algebra_Group_Subgroup_Lattice
import Definitions.Def_MillerRabin_FermatProbable
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Val2
import Definitions.Def_MillerRabin_StrongProbable
import Theorems.Thm_FPP_orderOf_dvd_sub_one

set_option autoImplicit false
open Nat
open SPP

theorem SPP.orderOf_dvd_sub_one {n : ℕ} {a : ZMod n} (h : SPP n a) :
    orderOf a ∣ n - 1 := by sorry
