-- Prove2me | Theorems.Thm_TypeDensity_polynomial_root_unique_of_derivative_isUnit
-- name    : TypeDensity.polynomial_root_unique_of_derivative_isUnit
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:30:27.137978+00:00
-- url     : https://prove2.me/theorems/2ce6a305-d2bd-4662-b74e-1064eeab68cc
-- title:
--   Hensel uniqueness: two roots of `f` congruent modulo the maximal ideal coincide when `f'(x)` is a unit.
-- statement:
--   Hensel uniqueness: two roots of `f` congruent modulo the maximal ideal coincide when `f'(x)` is a unit.
-- source:
--   TypeDensity/Surfaces/PowerSeries.lean#L391-L408

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PicardGroup
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.polynomial_root_unique_of_derivative_isUnit (S : Type) [CommRing S] [IsLocalRing S]
    (f : Polynomial S) (x y : S) (hx : Polynomial.eval x f = 0) (hy : Polynomial.eval y f = 0)
    (hxy : y - x ∈ IsLocalRing.maximalIdeal S)
    (hd : IsUnit (Polynomial.eval x (Polynomial.derivative f))) :
    y = x := by sorry
