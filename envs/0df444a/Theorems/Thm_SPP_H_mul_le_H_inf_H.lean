-- Prove2me | Theorems.Thm_SPP_H_mul_le_H_inf_H
-- name    : SPP.H_mul_le_H_inf_H
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:10:00.207745+00:00
-- url     : https://prove2.me/theorems/666a0a9e-bd93-494b-8d15-6cb86e9a12b1
-- title:
--   SPP: H mul le H inf H
-- statement:
--   The SPP construction uses the H mul le H inf H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L506-L508
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L506-L508

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

theorem SPP.H_mul_le_H_inf_H {m₁ m₂ : ℕ} (h : m₁ * m₂ ∣ n) :
    H h ≤ H (dvd_of_mul_right_dvd h) ⊓ H (dvd_of_mul_left_dvd h) := by sorry
