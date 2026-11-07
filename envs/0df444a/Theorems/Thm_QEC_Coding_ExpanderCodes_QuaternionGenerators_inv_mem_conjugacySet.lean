-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_inv_mem_conjugacySet
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.inv_mem_conjugacySet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:44:26.510203+00:00
-- url     : https://prove2.me/theorems/ed186a51-9cbf-4a68-bb2c-7dec52799d4a
-- title:
--   Quaternion Generators: inv mem conjugacy Set
-- statement:
--   One conjugation realizing the inverse makes the whole orbit inverse closed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionCayleySets.lean#L65-L75
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionCayleySets.lean#L65-L75

import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionGenerators
import Mathlib.GroupTheory.Subgroup.Centralizer
import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionCayleySets
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
universe u
variable {K : Type u} [Field K]
variable {H : Type*} [Group H]

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.inv_mem_conjugacySet (T : Subgroup H) (a u : H) (hu : u ∈ T)
    (hInverse : u * a * u⁻¹ = a⁻¹) {g : H} (hg : g ∈ conjugacySet T a) :
    g⁻¹ ∈ conjugacySet T a := by sorry
