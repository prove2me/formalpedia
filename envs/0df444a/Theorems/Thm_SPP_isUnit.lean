-- Prove2me | Theorems.Thm_SPP_isUnit
-- name    : SPP.isUnit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:03:50.039821+00:00
-- url     : https://prove2.me/theorems/8b80ae27-c0e0-417f-b1ad-6929717d2fe1
-- title:
--   SPP: is Unit
-- statement:
--   The SPP construction uses the is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L156-L158
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L156-L158

import Mathlib
import Definitions.Def_MillerRabin_Mathlib_Data_Fintype_Units
import Definitions.Def_MillerRabin_Mathlib_Algebra_Group_Subgroup_Lattice
import Definitions.Def_MillerRabin_FermatProbable
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Val2
import Definitions.Def_MillerRabin_StrongProbable
import Theorems.Thm_FPP_isUnit

set_option autoImplicit false
open Nat
open SPP

theorem SPP.isUnit {n : ℕ} [Fact (1 < n)] {a : ZMod n} (h : SPP n a) :
    IsUnit a := by sorry
