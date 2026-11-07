-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_projectiveBase_matrix_mem_psl_iff
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.projectiveBase_matrix_mem_psl_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:32:28.23139+00:00
-- url     : https://prove2.me/theorems/f2c48251-38aa-4216-b795-055686841b74
-- title:
--   Quaternion Generators: projective Base matrix mem psl iff
-- statement:
--   Membership of the first arithmetic generator in PSL₂ is an explicit
--   square condition; it is not implied merely by quaternion splitting.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionMatrix.lean#L146-L156
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionMatrix.lean#L146-L156

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

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.projectiveBase_matrix_mem_psl_iff (r y : K) (hR : r ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    projectiveMatrixEquiv r y hR hOne hTwo (projectiveBase (r ^ 2) y hY hOne) ∈
      ProjectiveDeterminant.specialProjectiveSubgroup ↔
      ∃ s : K, s ^ 2 = y / (1 + y) := by sorry
