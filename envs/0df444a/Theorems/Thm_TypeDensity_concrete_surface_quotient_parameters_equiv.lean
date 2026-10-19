-- Prove2me | Theorems.Thm_TypeDensity_concrete_surface_quotient_parameters_equiv
-- name    : TypeDensity.concrete_surface_quotient_parameters_equiv
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:49.757994+00:00
-- url     : https://prove2.me/theorems/da9ef045-cbb0-4bc2-b060-2760f2cea547
-- title:
--   The concrete surface modulo `(t, x)` is the residue field of `O`.
-- statement:
--   The concrete surface modulo `(t, x)` is the residue field of `O`.
-- source:
--   TypeDensity/Surfaces/PowerSeries.lean#L897-L950

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Theorems.Thm_TypeDensity_surfaceRelation_constantCoeff
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

theorem TypeDensity.concrete_surface_quotient_parameters_equiv (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ)
    (ha : 0 < a) :
    ∃ e : (ConcreteSurface O pi u a b ⧸ surfaceParameterIdeal O pi u a b) ≃+*
    IsLocalRing.ResidueField O, ∀ s :
    TwoSeries O, e (Ideal.Quotient.mk (surfaceParameterIdeal O pi u a b) (surfaceMk O pi u a b s)) =
    IsLocalRing.residue O (MvPowerSeries.constantCoeff s) := by sorry
