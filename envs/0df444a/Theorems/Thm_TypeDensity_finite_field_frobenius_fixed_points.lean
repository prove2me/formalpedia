-- Prove2me | Theorems.Thm_TypeDensity_finite_field_frobenius_fixed_points
-- name    : TypeDensity.finite_field_frobenius_fixed_points
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:08.262293+00:00
-- url     : https://prove2.me/theorems/f156ddda-c1c8-41e8-b943-b648697948ee
-- title:
--   For a finite field `k ↪ K`, the solutions of `x^q = x` in the field `K` are exactly the image of `k`.
-- statement:
--   For a finite field `k ↪ K`, the solutions of `x^q = x` in the field `K` are exactly the image of `k`.
-- source:
--   TypeDensity/Unramified/Extension.lean#L523-L558

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

theorem TypeDensity.finite_field_frobenius_fixed_points (k K : Type) [Field k] [Finite k] [Field K]
    (ρ : k →+* K) (x : K) :
    x ^ Nat.card k = x ↔ x ∈ Set.range ρ := by sorry
