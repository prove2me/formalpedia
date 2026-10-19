-- Prove2me | Theorems.Thm_TypeDensity_distinct_monic_irreducible_coprime
-- name    : TypeDensity.distinct_monic_irreducible_coprime
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:11.7222+00:00
-- url     : https://prove2.me/theorems/f48c98fb-cf29-44d1-b68d-2d8e720607c6
-- title:
--   Distinct monic irreducible polynomials over a field are coprime.
-- statement:
--   Distinct monic irreducible polynomials over a field are coprime.
-- source:
--   TypeDensity/Unramified/Extension.lean#L445-L451

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

theorem TypeDensity.distinct_monic_irreducible_coprime (K : Type) [Field K] (g h : Polynomial K) (hg : g.Monic)
    (hh : h.Monic) (hgi : Irreducible g) (hhi : Irreducible h) (hne : g ≠ h) :
    IsCoprime g h := by sorry
