-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_ProjectiveIndex_generatedProjectiveImage_eq_top
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex.generatedProjectiveImage_eq_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:38:22.009196+00:00
-- url     : https://prove2.me/theorems/4a35d893-191a-46cd-a32f-4e8b0b73cd9b
-- title:
--   Projective Index: generated Projective Image eq top
-- statement:
--   A full-order determinant class supplies the whole projective group.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/FiniteImage.lean#L53-L66
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/FiniteImage.lean#L53-L66

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Index
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_FiniteImage
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex
variable {G Q : Type*} [Group G] [Group Q]
variable (n K : Type*) [Fintype n] [DecidableEq n]
  [Nonempty n] [Field K] [Fintype K]

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex.generatedProjectiveImage_eq_top
    (b : PGL(n, K))
    (horder : orderOf (projectiveDetClass n K b) =
      Nat.card (DetPowerClass n K)) :
    generatedProjectiveImage n K b = ⊤ := by sorry
