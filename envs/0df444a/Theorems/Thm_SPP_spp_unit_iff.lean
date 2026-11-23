-- Prove2me | Theorems.Thm_SPP_spp_unit_iff
-- name    : SPP.spp_unit_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:03:16.859035+00:00
-- url     : https://prove2.me/theorems/015a8e40-1ec4-4ccb-8fcf-b33b25dbe80c
-- title:
--   SPP: spp unit iff
-- statement:
--   The SPP construction uses the spp unit iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L180-L183
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L180-L183

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

theorem SPP.spp_unit_iff {a : (ZMod n)ˣ} :
    SPP n a ↔ a ^ oddPart (n - 1) = 1 ∨
      ∃ s : ℕ, s < val₂ (n - 1) ∧ a ^ (2 ^ s * oddPart (n - 1)) = -1 := by sorry
