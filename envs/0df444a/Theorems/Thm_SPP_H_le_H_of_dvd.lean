-- Prove2me | Theorems.Thm_SPP_H_le_H_of_dvd
-- name    : SPP.H_le_H_of_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:04:56.999319+00:00
-- url     : https://prove2.me/theorems/095dab46-eb01-4538-b899-24df6d7272d1
-- title:
--   SPP: H le H of dvd
-- statement:
--   The SPP construction uses the H le H of dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L495-L504
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L495-L504

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

theorem SPP.H_le_H_of_dvd {m₁ m₂ : ℕ} (h₁ : m₁ ∣ m₂) (h₂ : m₂ ∣ n) :
    H h₂ ≤ H (h₁.trans h₂) := by sorry
