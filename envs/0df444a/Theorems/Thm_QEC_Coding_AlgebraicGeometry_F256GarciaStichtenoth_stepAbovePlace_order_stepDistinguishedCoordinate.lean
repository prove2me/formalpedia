-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepAbovePlace_order_stepDistinguishedCoordinate
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepAbovePlace_order_stepDistinguishedCoordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:54:27.502948+00:00
-- url     : https://prove2.me/theorems/953c2d9b-3f0f-4298-9a0f-03671c14d7e3
-- title:
--   F256 Garcia Stichtenoth: step Above Place order step Distinguished Coordinate
-- statement:
--   The next distinguished coordinate again has a normalized simple pole at
--   the chosen upper place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/PlaceStep.lean#L439-L443
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/PlaceStep.lean#L439-L443

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepAbovePlace_order_stepDistinguishedCoordinate
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    (stepAbovePlace P x hx).order (stepDistinguishedCoordinate P x hx) = -1 := by sorry
