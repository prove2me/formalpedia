-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_ProjectiveIndex_generalLinear_det_surjective
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex.generalLinear_det_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:36:08.414758+00:00
-- url     : https://prove2.me/theorems/a2908dea-f948-4988-9557-b28f1db3adcf
-- title:
--   Projective Index: general Linear det surjective
-- statement:
--   Determinant on `GL_d(K)` is onto when the index type is nonempty.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/Index.lean#L48-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/Index.lean#L48-L72

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Index
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex
variable (n K : Type*) [Fintype n] [DecidableEq n]
  [Nonempty n] [Field K] [Fintype K]
omit [Fintype K]

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex.generalLinear_det_surjective :
    Function.Surjective
      (Matrix.GeneralLinearGroup.det :
        Matrix.GeneralLinearGroup n K →* Kˣ) := by sorry
