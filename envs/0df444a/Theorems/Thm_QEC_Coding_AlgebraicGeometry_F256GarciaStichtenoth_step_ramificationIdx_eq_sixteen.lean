-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_step_ramificationIdx_eq_sixteen
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.step_ramificationIdx_eq_sixteen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:50:46.890543+00:00
-- url     : https://prove2.me/theorems/79e75d12-b71e-4a61-87eb-e59aad586229
-- title:
--   F256 Garcia Stichtenoth: step ramification Idx eq sixteen
-- statement:
--   The distinguished upper prime is totally ramified in the degree-sixteen
--   step.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/PlaceStep.lean#L246-L287
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/PlaceStep.lean#L246-L287

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Step
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Ideal.GoingUp
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_PlaceStep
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.step_ramificationIdx_eq_sixteen
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    (IsLocalRing.maximalIdeal P.valuationRing).ramificationIdx'
      (stepUpperIdeal P x hx) = 16 := by sorry
