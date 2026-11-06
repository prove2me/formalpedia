-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_map_maximalIdeal_eq_span_quadraticArtinSchreierIntegralUniformizer
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.map_maximalIdeal_eq_span_quadraticArtinSchreierIntegralUniformizer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:46:41.383446+00:00
-- url     : https://prove2.me/theorems/5523adbb-567f-4afc-b920-da27eb478610
-- title:
--   F256 Garcia Stichtenoth: map maximal Ideal eq span quadratic Artin Schreier Integral Uniformizer
-- statement:
--   The F256 Garcia Stichtenoth construction uses the map maximal Ideal eq span quadratic Artin Schreier Integral Uniformizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticStepDifferent.lean#L204-L215
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticStepDifferent.lean#L204-L215

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStep
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStepDifferent
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.map_maximalIdeal_eq_span_quadraticArtinSchreierIntegralUniformizer
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    Ideal.map
        (algebraMap P.valuationRing
          (QuadraticArtinSchreierIntegralClosure P a ha))
        (IsLocalRing.maximalIdeal P.valuationRing) =
      Ideal.span
        ({quadraticArtinSchreierIntegralUniformizer P a ha} :
          Set (QuadraticArtinSchreierIntegralClosure P a ha)) := by sorry
