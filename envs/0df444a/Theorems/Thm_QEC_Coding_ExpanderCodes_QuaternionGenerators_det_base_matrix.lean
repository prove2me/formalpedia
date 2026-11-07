-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_det_base_matrix
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.det_base_matrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:32:27.002193+00:00
-- url     : https://prove2.me/theorems/c60beee5-2349-4f20-9766-b4f02c25f80b
-- title:
--   Quaternion Generators: det base matrix
-- statement:
--   The Quaternion Generators construction uses the det base matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionMatrix.lean#L129-L134
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionMatrix.lean#L129-L134

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

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.det_base_matrix (r y : K) (hOne : 1 + y ≠ 0) :
    Matrix.det (matrixCoordinates r y (base (r ^ 2) y)) = y / (1 + y) := by sorry
