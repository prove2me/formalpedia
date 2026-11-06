-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepReciprocalRoot_ne_zero
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepReciprocalRoot_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:45:14.325949+00:00
-- url     : https://prove2.me/theorems/4da1d314-25bb-48bb-b2c0-7ae18729b786
-- title:
--   F256 Garcia Stichtenoth: step Reciprocal Root ne zero
-- statement:
--   The reciprocal Artin--Schreier root in a concrete step is nonzero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/Step.lean#L300-L326
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/Step.lean#L300-L326

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepReciprocalRoot_ne_zero (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) : stepReciprocalRoot P x hx ≠ 0 := by sorry
