-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_conjugacySet_total_nonconjugacy
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.conjugacySet_total_nonconjugacy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:44:35.101811+00:00
-- url     : https://prove2.me/theorems/a962ab55-2ec9-4d2a-aa31-620f3893e9c1
-- title:
--   Quaternion Generators: conjugacy Set total nonconjugacy
-- statement:
--   Separated squares prove nonconjugacy for all members of both orbits.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionCayleySets.lean#L84-L93
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionCayleySets.lean#L84-L93

import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionGenerators
import Mathlib.GroupTheory.Subgroup.Centralizer
import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionCayleySets
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
universe u
variable {K : Type u} [Field K]
variable {H : Type*} [Group H]

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.conjugacySet_total_nonconjugacy (T U : Subgroup H) (a b : H)
    (ha : a ^ 2 ≠ 1) (hb : b ^ 2 = 1)
    {x y : H} (hx : x ∈ conjugacySet T a) (hy : y ∈ conjugacySet U b) (g : H) :
    x * g ≠ g * y := by sorry
