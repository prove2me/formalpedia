-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepIntegralRoot_not_mem_upperIdeal_sq
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepIntegralRoot_not_mem_upperIdeal_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:49:58.038192+00:00
-- url     : https://prove2.me/theorems/c2f5134b-b68d-4db4-bf71-a1204aefe56e
-- title:
--   F256 Garcia Stichtenoth: source Step Integral Root not mem upper Ideal sq
-- statement:
--   The F256 Garcia Stichtenoth construction uses the source Step Integral Root not mem upper Ideal sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceStep.lean#L729-L792
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceStep.lean#L729-L792

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepIntegralRoot_not_mem_upperIdeal_sq
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    sourceStepIntegralRoot P x hx ∉ (sourceStepUpperIdeal P x hx) ^ 2 := by sorry
