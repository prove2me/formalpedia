-- Prove2me | Theorems.Thm_TypeDensity_concrete_surface_pi_regular
-- name    : TypeDensity.concrete_surface_pi_regular
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:01.335719+00:00
-- url     : https://prove2.me/theorems/86c1ddc7-2bef-468d-9b5f-bfe8344ccf28
-- title:
--   `π` is a nonzerodivisor in the concrete surface.
-- statement:
--   `π` is a nonzerodivisor in the concrete surface.
-- source:
--   TypeDensity/Surfaces/PowerSeries.lean#L711-L752

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Theorems.Thm_TypeDensity_residueSeries_ker
import Theorems.Thm_TypeDensity_residueSeries_surfaceRelation
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

theorem TypeDensity.concrete_surface_pi_regular (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ) :
    Function.Injective
    (fun r : ConcreteSurface O pi u a b ↦ algebraMap O (ConcreteSurface O pi u a b) pi * r) := by sorry
