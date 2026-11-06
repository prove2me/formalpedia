-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepAbovePlace_order_coordinate
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepAbovePlace_order_coordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:54:28.883202+00:00
-- url     : https://prove2.me/theorems/bf3a79b7-87cf-4d96-87f0-45cfd05cd4c0
-- title:
--   F256 Garcia Stichtenoth: source Step Above Place order coordinate
-- statement:
--   The next source coordinate again has normalized order `-1`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceStep.lean#L862-L866
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceStep.lean#L862-L866

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepAbovePlace_order_coordinate
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    (sourceStepAbovePlace P x hx).order (sourceStepCoordinate P x hx) = -1 := by sorry
