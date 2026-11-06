-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepIntegralRoot_not_mem_upperIdeal_sq
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepIntegralRoot_not_mem_upperIdeal_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:50:53.691049+00:00
-- url     : https://prove2.me/theorems/1a8a6fe4-8816-4aab-9ae8-57f7fc8dcbd6
-- title:
--   F256 Garcia Stichtenoth: step Integral Root not mem upper Ideal sq
-- statement:
--   The F256 Garcia Stichtenoth construction uses the step Integral Root not mem upper Ideal sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/PlaceStep.lean#L298-L362
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/PlaceStep.lean#L298-L362

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepIntegralRoot_not_mem_upperIdeal_sq
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    stepIntegralRoot P x hx ∉ (stepUpperIdeal P x hx) ^ 2 := by sorry
