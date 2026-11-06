-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_map_maximalIdeal_eq_span_sourceStepIntegralUniformizer
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.map_maximalIdeal_eq_span_sourceStepIntegralUniformizer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:46:37.369241+00:00
-- url     : https://prove2.me/theorems/fbc9f5a9-6a57-4ea4-a710-8a5133eb5305
-- title:
--   F256 Garcia Stichtenoth: map maximal Ideal eq span source Step Integral Uniformizer
-- statement:
--   The F256 Garcia Stichtenoth construction uses the map maximal Ideal eq span source Step Integral Uniformizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceStep.lean#L621-L634
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceStep.lean#L621-L634

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.map_maximalIdeal_eq_span_sourceStepIntegralUniformizer
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Ideal.map (algebraMap P.valuationRing (SourceStepIntegralClosure P x hx))
        (IsLocalRing.maximalIdeal P.valuationRing) =
      Ideal.span ({sourceStepIntegralUniformizer P x hx} :
        Set (SourceStepIntegralClosure P x hx)) := by sorry
