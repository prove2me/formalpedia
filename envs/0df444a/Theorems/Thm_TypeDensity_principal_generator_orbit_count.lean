-- Prove2me | Theorems.Thm_TypeDensity_principal_generator_orbit_count
-- name    : TypeDensity.principal_generator_orbit_count
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:47.319969+00:00
-- url     : https://prove2.me/theorems/8a2f1478-6ecc-4183-a4d2-5119931b5870
-- title:
--   In a finite local ring, `#{generators of (f)} · #{a | a f = 0} = #Bˣ` for `f ≠ 0`.
-- statement:
--   In a finite local ring, `#{generators of (f)} · #{a | a f = 0} = #Bˣ` for `f ≠ 0`.
-- source:
--   TypeDensity/Measure/HenselProducts.lean#L919-L979

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
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
open MeasureTheory
open scoped BigOperators ENNReal

theorem TypeDensity.principal_generator_orbit_count (B : Type) [CommRing B] [IsLocalRing B] [Finite B] (f : B)
    (hf : f ≠ 0) :
    Nat.card {g : B // Ideal.span {g}=Ideal.span {f}} * Nat.card {a : B // a*f=0} =
      Nat.card Bˣ := by sorry
