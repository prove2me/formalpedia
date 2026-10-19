-- Prove2me | Theorems.Thm_TypeDensity_t_chart_nonrational_point_completion_equiv
-- name    : TypeDensity.t_chart_nonrational_point_completion_equiv
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:00:54.989521+00:00
-- url     : https://prove2.me/theorems/fc060713-35e4-4541-a11f-982aed4b58fe
-- title:
--   The completion of the `t`-chart at a non-rational point `(t, Φ(x/t))` is isomorphic to the child surface over `O[θ] = O[X]/(Φ)`, compatibly with the chart substitution, and the image of `θ` is the Hen
-- statement:
--   The completion of the `t`-chart at a non-rational point `(t, Φ(x/t))` is isomorphic to the child surface over `O[θ] = O[X]/(Φ)`, compatibly with the chart substitution, and the image of `θ` is the Hensel root of `Φ`.
-- source:
--   TypeDensity/Surfaces/ChartCompletions.lean#L631-L726

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
import Theorems.Thm_TypeDensity_chart_child_completion_equiv
import Theorems.Thm_TypeDensity_chart_child_map_exists
import Theorems.Thm_TypeDensity_chart_point_quotient_adjoinRoot_equiv
import Theorems.Thm_TypeDensity_chart_nonrational_point_span_eq_comap
import Theorems.Thm_TypeDensity_unramified_lift_map_parameter_quotient_irreducible
import Theorems.Thm_TypeDensity_chartSubst_apply_generators
import Theorems.Thm_TypeDensity_chartSubst_surfaceRelation_base_change_and_x_chart
import Theorems.Thm_TypeDensity_polynomial_root_unique_of_derivative_isUnit
import Theorems.Thm_TypeDensity_concrete_surface_quotient_parameters_equiv
import Theorems.Thm_TypeDensity_concrete_surface_parameterIdeal_isMaximal
import Theorems.Thm_TypeDensity_concrete_surface_maximalIdeal_eq
import Theorems.Thm_TypeDensity_concrete_surface_isLocalRing
import Theorems.Thm_TypeDensity_blowupChart_concrete_isNoetherianRing
import Theorems.Thm_TypeDensity_nonrational_point_residue_surjective
import Theorems.Thm_TypeDensity_chart_child_completion_map_exists
import Theorems.Thm_TypeDensity_chart_child_completion_map_local
import Theorems.Thm_TypeDensity_simple_root_derivative_unit
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

theorem TypeDensity.t_chart_nonrational_point_completion_equiv (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ)
    (ha : 0 < a) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ)
    (hθ : IsUnit (AdjoinRoot.root Φ)) (P : Ideal ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)))) [P.IsPrime]
    (hP : P = Ideal.span
      {(chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) (surfaceT O pi u a b),
      Polynomial.eval₂ (((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))).comp (algebraMap O (ConcreteSurface O pi u a b)))
          ((chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) Φ}) :
    ∃ Eq : CompletedLocalAt ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) P ≃+* (ConcreteSurface (AdjoinRoot Φ) (algebraMap O (AdjoinRoot Φ) pi) (substUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ) (baseChangeUnit O (algebraMap O (AdjoinRoot Φ)) u) * shiftUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ) hθ ^ b) (a + b) 0),
      (∀ s : TwoSeries O,
        Eq (completedPointMap ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) P ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) (surfaceMk O pi u a b s))) =
          surfaceMk (AdjoinRoot Φ) (algebraMap O (AdjoinRoot Φ) pi) ((substUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ) (baseChangeUnit O (algebraMap O (AdjoinRoot Φ)) u) * shiftUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ) hθ ^ b)) (a + b) 0
            (chartSubst (AdjoinRoot Φ) (AdjoinRoot.root Φ)
              (MvPowerSeries.map (algebraMap O (AdjoinRoot Φ)) s))) ∧
      Eq (completedPointMap ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) P ((chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)))) =
        surfaceX (AdjoinRoot Φ) (algebraMap O (AdjoinRoot Φ) pi) ((substUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ) (baseChangeUnit O (algebraMap O (AdjoinRoot Φ)) u) * shiftUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ) hθ ^ b)) (a + b) 0 +
          algebraMap (AdjoinRoot Φ) ((ConcreteSurface (AdjoinRoot Φ) (algebraMap O (AdjoinRoot Φ) pi) (substUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ) (baseChangeUnit O (algebraMap O (AdjoinRoot Φ)) u) * shiftUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ) hθ ^ b) (a + b) 0)) (AdjoinRoot.root Φ) ∧
      (∀ c : O,
        Eq (completedPointMap ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) P
            ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) (algebraMap O (ConcreteSurface O pi u a b) c))) =
          algebraMap (AdjoinRoot Φ) ((ConcreteSurface (AdjoinRoot Φ) (algebraMap O (AdjoinRoot Φ) pi) (substUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ) (baseChangeUnit O (algebraMap O (AdjoinRoot Φ)) u) * shiftUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ) hθ ^ b) (a + b) 0))
            (algebraMap O (AdjoinRoot Φ) c)) ∧
      Polynomial.eval₂ ((completedPointMap ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) P).comp
          (((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))).comp (algebraMap O (ConcreteSurface O pi u a b))))
        (Eq.symm (algebraMap (AdjoinRoot Φ) ((ConcreteSurface (AdjoinRoot Φ) (algebraMap O (AdjoinRoot Φ) pi) (substUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ) (baseChangeUnit O (algebraMap O (AdjoinRoot Φ)) u) * shiftUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ) hθ ^ b) (a + b) 0)) (AdjoinRoot.root Φ)))
        Φ = 0 ∧
      Eq.symm (algebraMap (AdjoinRoot Φ) ((ConcreteSurface (AdjoinRoot Φ) (algebraMap O (AdjoinRoot Φ) pi) (substUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ) (baseChangeUnit O (algebraMap O (AdjoinRoot Φ)) u) * shiftUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ) hθ ^ b) (a + b) 0)) (AdjoinRoot.root Φ)) -
          completedPointMap ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) P ((chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) ∈
        (IsLocalRing.maximalIdeal (Localization.AtPrime P)).map
          (localCompletionMap (Localization.AtPrime P)) := by sorry
