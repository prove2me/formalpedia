-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_projectiveMatrixEquiv_mem_psl_iff
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.projectiveMatrixEquiv_mem_psl_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:32:18.247429+00:00
-- url     : https://prove2.me/theorems/6f544ad8-1f8f-4a87-8e61-429774f0ece5
-- title:
--   Quaternion Generators: projective Matrix Equiv mem psl iff
-- statement:
--   The precise norm-square condition for a quaternion unit to give a PSL₂ class.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionMatrix.lean#L116-L127
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionMatrix.lean#L116-L127

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

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.projectiveMatrixEquiv_mem_psl_iff (r y : K) (hR : r ≠ 0)
    (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) (q : (Model (r ^ 2) y)ˣ) :
    projectiveMatrixEquiv r y hR hOne hTwo (QuotientGroup.mk q) ∈
      ProjectiveDeterminant.specialProjectiveSubgroup ↔
      ∃ s : K, s ^ 2 =
        (q : Model (r ^ 2) y).re ^ 2 - r ^ 2 * (q : Model (r ^ 2) y).imI ^ 2 -
          (1 + y) * (q : Model (r ^ 2) y).imJ ^ 2 +
          r ^ 2 * (1 + y) * (q : Model (r ^ 2) y).imK ^ 2 := by sorry
