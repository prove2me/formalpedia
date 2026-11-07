-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_det_matrixCoordinates
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.det_matrixCoordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:32:19.769148+00:00
-- url     : https://prove2.me/theorems/4932781f-ac7e-4f1c-9325-eb8ad93e1eaa
-- title:
--   Quaternion Generators: det matrix Coordinates
-- statement:
--   Matrix determinant agrees with the norm derived from quaternion conjugation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionMatrix.lean#L62-L67
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionMatrix.lean#L62-L67

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

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.det_matrixCoordinates (r y : K) (q : Model (r ^ 2) y) :
    Matrix.det (matrixCoordinates r y q) =
      q.re ^ 2 - r ^ 2 * q.imI ^ 2 - (1 + y) * q.imJ ^ 2 +
        r ^ 2 * (1 + y) * q.imK ^ 2 := by sorry
