-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_ProjectiveIndex_projectiveDetClass_surjective
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex.projectiveDetClass_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:36:35.324202+00:00
-- url     : https://prove2.me/theorems/84444cb3-fbfc-4c8e-ab8e-f74528ec8682
-- title:
--   Projective Index: projective Det Class surjective
-- statement:
--   The projective determinant-class map is onto.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/Index.lean#L75-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/Index.lean#L75-L83

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Index
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex
variable (n K : Type*) [Fintype n] [DecidableEq n]
  [Nonempty n] [Field K] [Fintype K]

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex.projectiveDetClass_surjective :
    Function.Surjective (projectiveDetClass n K) := by sorry
