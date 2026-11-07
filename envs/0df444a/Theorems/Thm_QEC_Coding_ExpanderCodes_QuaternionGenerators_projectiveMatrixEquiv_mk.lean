-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_projectiveMatrixEquiv_mk
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.projectiveMatrixEquiv_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:32:02.933114+00:00
-- url     : https://prove2.me/theorems/85136563-22c6-469a-b88a-d996b1a12da8
-- title:
--   Quaternion Generators: projective Matrix Equiv mk
-- statement:
--   The Quaternion Generators construction uses the projective Matrix Equiv mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionMatrix.lean#L109-L113
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionMatrix.lean#L109-L113

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

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.projectiveMatrixEquiv_mk (r y : K) (hR : r ≠ 0)
    (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) (q : (Model (r ^ 2) y)ˣ) :
    projectiveMatrixEquiv r y hR hOne hTwo (QuotientGroup.mk q) =
      Matrix.ProjGenLinGroup.mk
        (Units.mapEquiv (matrixEquiv r y hR hOne hTwo).toMulEquiv q) := by sorry

attribute [defeq] QEC.Coding.ExpanderCodes.QuaternionGenerators.projectiveMatrixEquiv_mk
