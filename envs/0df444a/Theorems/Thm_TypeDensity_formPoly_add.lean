-- Prove2me | Theorems.Thm_TypeDensity_formPoly_add
-- name    : TypeDensity.formPoly_add
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:05.192645+00:00
-- url     : https://prove2.me/theorems/89891170-2bdb-4319-86e3-ece0493c0ea9
-- title:
--   `formPoly` is additive.
-- statement:
--   `formPoly` is additive.
-- source:
--   TypeDensity/Unramified/Extension.lean#L669-L672

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
set_option autoImplicit false

open TypeDensity
open Polynomial IsLocalRing MeasureTheory
variable {A : Type} [CommRing A] {n : ℕ}

theorem TypeDensity.formPoly_add (a b : Fin (n + 1) → A) :
    formPoly (a + b) = formPoly a + formPoly b := by sorry
