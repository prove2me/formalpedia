-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepAbovePlace_order_integral_eq_multiplicity
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepAbovePlace_order_integral_eq_multiplicity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:51:03.34841+00:00
-- url     : https://prove2.me/theorems/9520b5d9-8279-4ccf-9909-33a059d36b51
-- title:
--   F256 Garcia Stichtenoth: step Above Place order integral eq multiplicity
-- statement:
--   At the distinguished upper place, the order of a nonzero integral
--   element is its multiplicity at the chosen upper prime.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/PlaceStep.lean#L411-L422
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/PlaceStep.lean#L411-L422

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepAbovePlace_order_integral_eq_multiplicity
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    {y : StepIntegralClosure P x hx} (hy : y ≠ 0) :
    (stepAbovePlace P x hx).order
        (algebraMap (StepIntegralClosure P x hx) (StepField P x hx) y) =
      (multiplicity (stepUpperIdeal P x hx) (Ideal.span {y}) : ℤ) := by sorry
