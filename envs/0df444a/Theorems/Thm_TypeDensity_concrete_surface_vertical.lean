-- Prove2me | Theorems.Thm_TypeDensity_concrete_surface_vertical
-- name    : TypeDensity.concrete_surface_vertical
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:54.21288+00:00
-- url     : https://prove2.me/theorems/e96e00c1-b2b1-4cd5-9256-63f1c006e260
-- title:
--   The vertical equation `π = u · t^a · x^b` holds in the concrete surface.
-- statement:
--   The vertical equation `π = u · t^a · x^b` holds in the concrete surface.
-- source:
--   TypeDensity/Surfaces/Lengths.lean#L768-L779

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

theorem TypeDensity.concrete_surface_vertical (O : Type) [CommRing O] (pi : O) (u : (TwoSeries O)ˣ) (a b : ℕ) :
    algebraMap O (ConcreteSurface O pi u a b) pi =
    (surfaceUnit O pi u a b : ConcreteSurface O pi u a b) * surfaceT O pi u a b ^ a *
    surfaceX O pi u a b ^ b := by sorry
