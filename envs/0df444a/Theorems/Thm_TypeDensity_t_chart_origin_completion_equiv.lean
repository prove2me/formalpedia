-- Prove2me | Theorems.Thm_TypeDensity_t_chart_origin_completion_equiv
-- name    : TypeDensity.t_chart_origin_completion_equiv
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:15:02.317305+00:00
-- url     : https://prove2.me/theorems/cf254940-1466-4051-a029-3c95e66fb6c7
-- title:
--   The completion of the `t`-chart at its origin `(t, x/t)` is the concrete surface with unit `substUnit O 0 u` and exponents `(a + b, b)`, compatibly with the chart substitution.
-- statement:
--   The completion of the `t`-chart at its origin `(t, x/t)` is the concrete surface with unit `substUnit O 0 u` and exponents `(a + b, b)`, compatibly with the chart substitution.
-- source:
--   TypeDensity/Surfaces/ChartCompletions.lean#L797-L821

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
import Theorems.Thm_TypeDensity_rational_point_completion_equiv
import Theorems.Thm_TypeDensity_chartSubst_apply_generators
import Theorems.Thm_TypeDensity_chartSubst_surfaceRelation_origin_and_unit_point
import Theorems.Thm_TypeDensity_concrete_surface_parameterIdeal_isMaximal
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

theorem TypeDensity.t_chart_origin_completion_equiv (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ)
    (ha : 0 < a) (P : Ideal ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)))) [P.IsPrime]
    (hP : P = Ideal.span {(chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) (surfaceT O pi u a b), (chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))}) :
    ∃ Eq : CompletedLocalAt ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) P ≃+* ConcreteSurface O pi (substUnit O 0 u) (a + b)
        b,
      (∀ s : TwoSeries O,
        Eq (completedPointMap ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) P ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) (surfaceMk O pi u a b s))) =
            surfaceMk O pi
        (substUnit O 0 u) (a + b) b (chartSubst O 0 s)) ∧ Eq (completedPointMap ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)))
            P ((chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)))) =
      surfaceX O pi (substUnit O 0 u) (a + b) b ∧ ∀ c : O,
      Eq (completedPointMap ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) P ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))
          (algebraMap O (ConcreteSurface O pi u a b) c))) =
      algebraMap O (ConcreteSurface O pi (substUnit O 0 u) (a + b) b) c := by sorry
