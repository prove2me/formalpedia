-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_ProjectiveIndex_projectiveDetClass_mk
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex.projectiveDetClass_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:36:19.148587+00:00
-- url     : https://prove2.me/theorems/25c3f0e6-4c6f-448f-b205-fa262435b449
-- title:
--   Projective Index: projective Det Class mk
-- statement:
--   The Projective Index construction uses the projective Det Class mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/Index.lean#L40-L44
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/Index.lean#L40-L44

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Index
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex
variable (n K : Type*) [Fintype n] [DecidableEq n]
  [Nonempty n] [Field K] [Fintype K]
omit [Nonempty n]

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex.projectiveDetClass_mk
    (g : Matrix.GeneralLinearGroup n K) :
    projectiveDetClass n K (Matrix.ProjGenLinGroup.mk g) =
      QuotientGroup.mk' _ (Matrix.GeneralLinearGroup.det g) := by sorry
