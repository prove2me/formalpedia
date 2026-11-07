-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_det_prime_matrix
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.det_prime_matrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:32:29.747475+00:00
-- url     : https://prove2.me/theorems/51d0bd65-baeb-4c7b-a207-7b40cf8134c5
-- title:
--   Quaternion Generators: det prime matrix
-- statement:
--   The Quaternion Generators construction uses the det prime matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionMatrix.lean#L136-L142
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionMatrix.lean#L136-L142

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

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.det_prime_matrix (r y : K) (hOne : 1 + y ≠ 0) :
    Matrix.det (matrixCoordinates r y (prime (r ^ 2) y)) =
      -(r ^ 2) * y / (1 + y) := by sorry
