-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepIntegralClosure_adjoin_root_eq_top
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepIntegralClosure_adjoin_root_eq_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:49:58.837193+00:00
-- url     : https://prove2.me/theorems/99279ba0-c6da-4067-8985-e88163476e9e
-- title:
--   F256 Garcia Stichtenoth: source Step Integral Closure adjoin root eq top
-- statement:
--   The F256 Garcia Stichtenoth construction uses the source Step Integral Closure adjoin root eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceStep.lean#L941-L1017
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceStep.lean#L941-L1017

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepIntegralClosure_adjoin_root_eq_top
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Algebra.adjoin P.valuationRing
        ({sourceStepIntegralRoot P x hx} :
          Set (SourceStepIntegralClosure P x hx)) = ⊤ := by sorry
