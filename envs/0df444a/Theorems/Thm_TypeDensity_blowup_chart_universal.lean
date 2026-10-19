-- Prove2me | Theorems.Thm_TypeDensity_blowup_chart_universal
-- name    : TypeDensity.blowup_chart_universal
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:30:34.867519+00:00
-- url     : https://prove2.me/theorems/c5085b13-0c28-4282-a074-97513d6db9fb
-- title:
--   Universal property of the `t`-chart: a map `φ : R → S` with an element `z` satisfying `φ t · z = φ x` extends uniquely through `R[X]/(tX − x)` sending the slope to `z`.
-- statement:
--   Universal property of the `t`-chart: a map `φ : R → S` with an element `z` satisfying `φ t · z = φ x` extends uniquely through `R[X]/(tX − x)` sending the slope to `z`.
-- source:
--   TypeDensity/Blowup/Charts.lean#L840-L852

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Blowup_Charts
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
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PicardGroup
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.blowup_chart_universal (R S : Type) [CommRing R] [CommRing S] (t x : R) (phi : R →+* S)
    (z : S) (hz : phi t * z = phi x) :
    ∃ psi : BlowupChart R t x →+* S, (∀ a : R, psi (chartBase R t x a) = phi a) ∧ psi
        (chartSlope R t x) = z := by sorry
