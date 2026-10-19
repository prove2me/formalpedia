-- Prove2me | Theorems.Thm_TypeDensity_concrete_surface_isNoetherianRing
-- name    : TypeDensity.concrete_surface_isNoetherianRing
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:40.436408+00:00
-- url     : https://prove2.me/theorems/756e5457-70f8-48f8-8d2b-4fe7cebf0314
-- title:
--   The concrete surface over a Noetherian ring is Noetherian.
-- statement:
--   The concrete surface over a Noetherian ring is Noetherian.
-- source:
--   TypeDensity/Surfaces/Lengths.lean#L716-L720

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
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

theorem TypeDensity.concrete_surface_isNoetherianRing (O : Type) [CommRing O] (pi : O) (u : (TwoSeries O)ˣ)
    (a b : ℕ) [IsNoetherianRing O] :
    IsNoetherianRing (ConcreteSurface O pi u a b) := by sorry
