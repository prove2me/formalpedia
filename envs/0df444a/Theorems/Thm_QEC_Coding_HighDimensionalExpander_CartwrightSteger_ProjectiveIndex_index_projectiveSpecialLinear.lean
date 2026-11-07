-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_ProjectiveIndex_index_projectiveSpecialLinear
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex.index_projectiveSpecialLinear
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:37:55.052986+00:00
-- url     : https://prove2.me/theorems/ab225915-dd08-4d63-8396-913c2f596875
-- title:
--   Projective Index: index projective Special Linear
-- statement:
--   Consequently, the index of `PSL_d(K)` in `PGL_d(K)` is the cardinality
--   of the determinant power-class group.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/Index.lean#L140-L145
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/Index.lean#L140-L145

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Index
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex
variable (n K : Type*) [Fintype n] [DecidableEq n]
  [Nonempty n] [Field K] [Fintype K]

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex.index_projectiveSpecialLinear :
    (projectiveSpecialLinear n K).index = Nat.card (DetPowerClass n K) := by sorry
