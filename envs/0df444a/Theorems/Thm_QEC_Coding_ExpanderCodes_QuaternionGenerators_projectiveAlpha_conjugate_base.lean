-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_projectiveAlpha_conjugate_base
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.projectiveAlpha_conjugate_base
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:44:33.671726+00:00
-- url     : https://prove2.me/theorems/62e4bfb1-8e4e-4dfd-8864-0dc75825e3fa
-- title:
--   Quaternion Generators: projective Alpha conjugate base
-- statement:
--   The inverse of the first generator is conjugate by the quadratic unit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionCayleySets.lean#L24-L41
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionCayleySets.lean#L24-L41

import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionGenerators
import Mathlib.GroupTheory.Subgroup.Centralizer
import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionCayleySets
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
universe u
variable {K : Type u} [Field K]

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.projectiveAlpha_conjugate_base (epsilon y : K) (hEpsilon : epsilon ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) :
    projectiveAlpha epsilon y hEpsilon * projectiveBase epsilon y hY hOne *
      (projectiveAlpha epsilon y hEpsilon)⁻¹ =
        (projectiveBase epsilon y hY hOne)⁻¹ := by sorry
