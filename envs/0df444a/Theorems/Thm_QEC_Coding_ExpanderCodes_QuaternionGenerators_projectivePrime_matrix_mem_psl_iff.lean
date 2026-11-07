-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_projectivePrime_matrix_mem_psl_iff
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.projectivePrime_matrix_mem_psl_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:32:31.175904+00:00
-- url     : https://prove2.me/theorems/b5ee5688-0254-4fc5-b4ba-39e41e2c32f6
-- title:
--   Quaternion Generators: projective Prime matrix mem psl iff
-- statement:
--   The Quaternion Generators construction uses the projective Prime matrix mem psl iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionMatrix.lean#L158-L170
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionMatrix.lean#L158-L170

import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionGenerators
import Definitions.Def_QEC_Coding_ExpanderCodes_ProjectiveDeterminant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.Algebra.Group.Units.Equiv
import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionMatrix
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
universe u
variable {K : Type u} [Field K]
open Matrix

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.projectivePrime_matrix_mem_psl_iff (r y : K) (hR : r ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    projectiveMatrixEquiv r y hR hOne hTwo
      (projectivePrime (r ^ 2) y (pow_ne_zero 2 hR) hY hOne) ∈
      ProjectiveDeterminant.specialProjectiveSubgroup ↔
      ∃ s : K, s ^ 2 = -(r ^ 2) * y / (1 + y) := by sorry
