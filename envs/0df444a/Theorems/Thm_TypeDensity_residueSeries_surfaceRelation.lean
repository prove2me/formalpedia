-- Prove2me | Theorems.Thm_TypeDensity_residueSeries_surfaceRelation
-- name    : TypeDensity.residueSeries_surfaceRelation
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:47.697727+00:00
-- url     : https://prove2.me/theorems/26cbe83a-3afa-4f30-a800-4c3541ffacb2
-- title:
--   The reduction of the surface relation is `-(ū T^a X^b)`.
-- statement:
--   The reduction of the surface relation is `-(ū T^a X^b)`.
-- source:
--   TypeDensity/Surfaces/PowerSeries.lean#L687-L701

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

theorem TypeDensity.residueSeries_surfaceRelation (O : Type) [CommRing O] [IsLocalRing O] (pi : O)
    (hpi : pi ∈ IsLocalRing.maximalIdeal O) (u : (TwoSeries O)ˣ) (a b : ℕ) :
    residueSeries O (surfaceRelation O pi u a b) =
    -(residueSeries O (u : TwoSeries O) * axisT (IsLocalRing.ResidueField O) ^ a *
      axisX (IsLocalRing.ResidueField O) ^ b) := by sorry
