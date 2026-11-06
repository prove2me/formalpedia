-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticArtinSchreierDifferentIdeal_multiplicity
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreierDifferentIdeal_multiplicity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:49:47.449863+00:00
-- url     : https://prove2.me/theorems/34246864-1426-4bc2-83e4-c66e15bea61a
-- title:
--   F256 Garcia Stichtenoth: quadratic Artin Schreier Different Ideal multiplicity
-- statement:
--   The quadratic simple-pole step has exact weak different exponent two.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticStepDifferent.lean#L673-L701
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticStepDifferent.lean#L673-L701

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreierDifferentIdeal_multiplicity
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    multiplicity (quadraticArtinSchreierUpperIdeal P a ha)
        (differentIdeal P.valuationRing
          (QuadraticArtinSchreierIntegralClosure P a ha)) = 2 := by sorry
