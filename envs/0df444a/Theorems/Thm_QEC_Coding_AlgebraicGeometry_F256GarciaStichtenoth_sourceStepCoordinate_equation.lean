-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepCoordinate_equation
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepCoordinate_equation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:54:07.305623+00:00
-- url     : https://prove2.me/theorems/b13da6de-b6fb-4c8c-abcc-2da0b36b4544
-- title:
--   F256 Garcia Stichtenoth: source Step Coordinate equation
-- statement:
--   One constructed step satisfies the source-facing recursion exactly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceStep.lean#L381-L407
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceStep.lean#L381-L407

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Step
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceStep
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepCoordinate_equation
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    sourceStepCoordinate P x hx ^ 16 + sourceStepCoordinate P x hx =
      sourceStepEmbedding P x hx (sourceStepRhs x) := by sorry
