-- Prove2me | Theorems.Thm_SPP_H_inf_H_lt_H_inf_H_inf_H
-- name    : SPP.H_inf_H_lt_H_inf_H_inf_H
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:06:26.363715+00:00
-- url     : https://prove2.me/theorems/67001465-1355-47fc-89d4-9b0ef65b742d
-- title:
--   SPP: H inf H lt H inf H inf H
-- statement:
--   The lemma mentioned above.
--   Only used for h := dvd_of_eq _, but this very convenient for type casting.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L512-L552
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L512-L552

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

theorem SPP.H_inf_H_lt_H_inf_H_inf_H [NeZero n] {m₁ m₂ m₃ : ℕ}
    (h₁ : 2 < m₁) (h₂ : 2 < m₂) (hc : m₁.Coprime (m₂ * m₃)) (h₁₂₃n : m₁ * m₂ * m₃ ∣ n) :
    H (dvd_of_mul_right_dvd h₁₂₃n) ⊓ H (dvd_of_mul_left_dvd h₁₂₃n) <
      H (dvd_of_mul_right_dvd (dvd_of_mul_right_dvd h₁₂₃n)) ⊓
      H (dvd_of_mul_left_dvd (dvd_of_mul_right_dvd h₁₂₃n)) ⊓ H (dvd_of_mul_left_dvd h₁₂₃n) := by sorry
