-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_ProjectiveIndex_ker_projectiveDetClass_eq_projectiveSpecialLinear
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex.ker_projectiveDetClass_eq_projectiveSpecialLinear
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:36:12.329018+00:00
-- url     : https://prove2.me/theorems/526f74d3-9c43-4ea4-81b5-f0ed43269c4e
-- title:
--   Projective Index: ker projective Det Class eq projective Special Linear
-- statement:
--   The kernel of determinant class is exactly `PSL_d(K)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/Index.lean#L91-L136
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/Index.lean#L91-L136

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Index
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex
variable (n K : Type*) [Fintype n] [DecidableEq n]
  [Nonempty n] [Field K] [Fintype K]

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex.ker_projectiveDetClass_eq_projectiveSpecialLinear :
    (projectiveDetClass n K).ker = projectiveSpecialLinear n K := by sorry
