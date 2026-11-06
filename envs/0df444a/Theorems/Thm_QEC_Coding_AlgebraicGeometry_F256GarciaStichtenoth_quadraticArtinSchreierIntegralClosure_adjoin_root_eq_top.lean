-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticArtinSchreierIntegralClosure_adjoin_root_eq_top
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreierIntegralClosure_adjoin_root_eq_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:49:24.9852+00:00
-- url     : https://prove2.me/theorems/a941247d-174d-406b-a90e-38ac25cb7d4a
-- title:
--   F256 Garcia Stichtenoth: quadratic Artin Schreier Integral Closure adjoin root eq top
-- statement:
--   The F256 Garcia Stichtenoth construction uses the quadratic Artin Schreier Integral Closure adjoin root eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticStepDifferent.lean#L539-L617
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticStepDifferent.lean#L539-L617

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreierIntegralClosure_adjoin_root_eq_top
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    Algebra.adjoin P.valuationRing
        ({quadraticArtinSchreierIntegralRoot P a ha} :
          Set (QuadraticArtinSchreierIntegralClosure P a ha)) = ⊤ := by sorry
