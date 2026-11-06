-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepReciprocalRoot_ne_zero
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepReciprocalRoot_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:48:23.875265+00:00
-- url     : https://prove2.me/theorems/1068410f-24c0-430d-b022-78f3b8a0b557
-- title:
--   F256 Garcia Stichtenoth: source Step Reciprocal Root ne zero
-- statement:
--   The F256 Garcia Stichtenoth construction uses the source Step Reciprocal Root ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceStep.lean#L323-L349
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceStep.lean#L323-L349

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepReciprocalRoot_ne_zero
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    sourceStepReciprocalRoot P x hx ≠ 0 := by sorry
