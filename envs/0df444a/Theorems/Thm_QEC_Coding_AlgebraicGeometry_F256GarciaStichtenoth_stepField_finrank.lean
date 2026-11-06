-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepField_finrank
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepField_finrank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:45:47.904437+00:00
-- url     : https://prove2.me/theorems/1632916f-8db6-4a9d-a791-d51570bf2d04
-- title:
--   F256 Garcia Stichtenoth: step Field finrank
-- statement:
--   The field degree of one actual recursion step.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/Step.lean#L417-L426
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/Step.lean#L417-L426

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_FixedFieldArtinSchreier
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Step
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepField_finrank (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :
    Module.finrank K (StepField P x hx) = 16 := by sorry
