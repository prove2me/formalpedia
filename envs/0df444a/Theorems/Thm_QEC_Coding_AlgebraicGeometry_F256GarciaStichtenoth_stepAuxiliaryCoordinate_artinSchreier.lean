-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepAuxiliaryCoordinate_artinSchreier
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepAuxiliaryCoordinate_artinSchreier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:45:46.584298+00:00
-- url     : https://prove2.me/theorems/6cee10c0-49b0-4f24-9ff8-4a240bea5131
-- title:
--   F256 Garcia Stichtenoth: step Auxiliary Coordinate artin Schreier
-- statement:
--   One recursion step satisfies the literal Garcia--Stichtenoth equation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/Step.lean#L360-L396
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/Step.lean#L360-L396

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepAuxiliaryCoordinate_artinSchreier
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    stepAuxiliaryCoordinate P x hx ^ 16 + stepAuxiliaryCoordinate P x hx =
      stepFieldEmbedding P x hx x ^ 17 := by sorry
