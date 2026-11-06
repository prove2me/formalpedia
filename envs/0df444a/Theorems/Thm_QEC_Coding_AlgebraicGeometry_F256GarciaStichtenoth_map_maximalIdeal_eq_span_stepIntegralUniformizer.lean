-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_map_maximalIdeal_eq_span_stepIntegralUniformizer
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.map_maximalIdeal_eq_span_stepIntegralUniformizer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:48:46.245226+00:00
-- url     : https://prove2.me/theorems/130ebcc8-06f7-4546-8e0e-6c4affb5eadc
-- title:
--   F256 Garcia Stichtenoth: map maximal Ideal eq span step Integral Uniformizer
-- statement:
--   The F256 Garcia Stichtenoth construction uses the map maximal Ideal eq span step Integral Uniformizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/PlaceStep.lean#L194-L202
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/PlaceStep.lean#L194-L202

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.map_maximalIdeal_eq_span_stepIntegralUniformizer
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Ideal.map (algebraMap P.valuationRing (StepIntegralClosure P x hx))
        (IsLocalRing.maximalIdeal P.valuationRing) =
      Ideal.span ({stepIntegralUniformizer P x hx} :
        Set (StepIntegralClosure P x hx)) := by sorry
