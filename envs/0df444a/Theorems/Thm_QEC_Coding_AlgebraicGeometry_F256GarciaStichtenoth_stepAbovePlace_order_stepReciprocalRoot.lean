-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepAbovePlace_order_stepReciprocalRoot
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepAbovePlace_order_stepReciprocalRoot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:51:09.28701+00:00
-- url     : https://prove2.me/theorems/51d552fe-9056-49df-bd5e-2bdaf9139437
-- title:
--   F256 Garcia Stichtenoth: step Above Place order step Reciprocal Root
-- statement:
--   The reciprocal Artin--Schreier root is a uniformizer at the chosen upper
--   place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/PlaceStep.lean#L426-L435
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/PlaceStep.lean#L426-L435

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepAbovePlace_order_stepReciprocalRoot
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    (stepAbovePlace P x hx).order (stepReciprocalRoot P x hx) = 1 := by sorry
