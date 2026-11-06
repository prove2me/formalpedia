-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticArtinSchreierAbovePlace_order_coordinate
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreierAbovePlace_order_coordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:49:21.851852+00:00
-- url     : https://prove2.me/theorems/14f04fce-9595-4215-b14e-08d04695b2a7
-- title:
--   F256 Garcia Stichtenoth: quadratic Artin Schreier Above Place order coordinate
-- statement:
--   The new Artin--Schreier coordinate again has normalized order `-1`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticStepDifferent.lean#L452-L457
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticStepDifferent.lean#L452-L457

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreierAbovePlace_order_coordinate
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    (quadraticArtinSchreierAbovePlace P a ha).order
      (quadraticArtinSchreierCoordinate P a ha) = -1 := by sorry
