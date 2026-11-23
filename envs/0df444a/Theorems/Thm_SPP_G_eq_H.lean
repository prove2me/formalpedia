-- Prove2me | Theorems.Thm_SPP_G_eq_H
-- name    : SPP.G_eq_H
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T08:09:46.772886+00:00
-- url     : https://prove2.me/theorems/bb9b8690-ede5-497a-bff1-1ceda26e9a11
-- title:
--   SPP: G eq H
-- statement:
--   The SPP construction uses the G eq H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L485-L486
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L485-L486

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

theorem SPP.G_eq_H : G n = H (dvd_refl n) := by sorry
