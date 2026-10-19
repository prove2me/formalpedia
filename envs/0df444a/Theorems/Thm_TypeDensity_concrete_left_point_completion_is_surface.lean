-- Prove2me | Theorems.Thm_TypeDensity_concrete_left_point_completion_is_surface
-- name    : TypeDensity.concrete_left_point_completion_is_surface
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:25:45.344482+00:00
-- url     : https://prove2.me/theorems/473579b8-0203-4037-9bf6-c80f2a2452a9
-- title:
--   The completion of the `t`-chart at any closed point over the closed point of the concrete surface is again a concrete surface over a complete discrete valuation ring, with `t ↦ t'`.
-- statement:
--   The completion of the `t`-chart at any closed point over the closed point of the concrete surface is again a concrete surface over a complete discrete valuation ring, with `t ↦ t'`.
-- source:
--   TypeDensity/Surfaces/ConcretePoints.lean#L188-L218

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Formula_FiniteFieldCounts
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Blowup_Charts
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_t_chart_nonrational_point_completion_equiv
import Theorems.Thm_TypeDensity_t_chart_origin_completion_equiv
import Theorems.Thm_TypeDensity_t_chart_unit_point_completion_equiv
import Theorems.Thm_TypeDensity_unramified_root_isUnit_of_two_le_natDegree
import Theorems.Thm_TypeDensity_concrete_chart_point_span_form
import Theorems.Thm_TypeDensity_chartSubst_apply_generators
import Theorems.Thm_TypeDensity_unramified_is_dvr
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
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.concrete_left_point_completion_is_surface (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a) (P : Ideal ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)))) [P.IsMaximal] [P.IsPrime]
    (hP : (chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) (surfaceT O pi u a b) ∈ P) :
    ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O')
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal O') O')
      (_ : Finite (IsLocalRing.ResidueField O')) (pi' : O') (u' : (TwoSeries O')ˣ) (a' b' : ℕ),
      Irreducible pi' ∧ 0 < a' ∧
      ∃ Eq : CompletedLocalAt ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) P ≃+* ConcreteSurface O' pi' u' a' b',
      Eq (completedPointMap ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) P ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) (surfaceT O pi u a b))) =
          surfaceT O' pi' u' a' b' := by sorry
