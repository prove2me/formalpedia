-- Prove2me | Theorems.Thm_TypeDensity_child_series_eval_comp_chart_subst
-- name    : TypeDensity.child_series_eval_comp_chart_subst
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:22.596366+00:00
-- url     : https://prove2.me/theorems/2a5a491d-6e7a-4d9e-a449-e0a60c6c4bc6
-- title:
--   The evaluation `Θ` of the child power series, composed with the chart substitution `s`, agrees with the canonical map from `O[[T,X]]` through the chart to its completion at `P`.
-- statement:
--   The evaluation `Θ` of the child power series, composed with the chart substitution `s`, agrees with the canonical map from `O[[T,X]]` through the chart to its completion at `P`.
-- source:
--   TypeDensity/Surfaces/Regularity.lean#L648-L689

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Blowup_Charts
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_blowup_chart_relation
import Theorems.Thm_TypeDensity_twoSeries_ringHom_ext_of_isNilpotent
import Theorems.Thm_TypeDensity_blowupChart_concrete_isNoetherianRing
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
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.child_series_eval_comp_chart_subst (O O' : Type) [CommRing O] [IsNoetherianRing O]
    [CommRing O'] (pi : O) (u : (TwoSeries O)ˣ) (a b : ℕ) (E F : TwoSeries O)
    (hEF : (E = axisT O ∧ F = axisX O) ∨ (E = axisX O ∧ F = axisT O))
    (P : Ideal
      (BlowupChart (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F)))
    [P.IsPrime]
    (hE : chartBase (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F)
      (surfaceMk O pi u a b E) ∈ P)
    (hF : chartBase (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F)
      (surfaceMk O pi u a b F) ∈ P) (ρ : O →+* O') (α : O') (s : TwoSeries O →+* TwoSeries O')
    (hsC : ∀ c : O, s (MvPowerSeries.C c) = MvPowerSeries.C (ρ c)) (hsE : s E = axisT O')
    (hsF : s F = axisT O' * (axisX O' + MvPowerSeries.C α))
    (κ : O' →+* CompletedLocalAt
      (BlowupChart (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F))
      P) (hκ : ∀ c : O,
      κ (ρ c) = completedPointMap
      (BlowupChart (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F)) P
      (chartBase (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F)
      (algebraMap O (ConcreteSurface O pi u a b) c)))
    (Θ : TwoSeries O' →+* CompletedLocalAt
      (BlowupChart (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F))
      P) (hΘC : ∀ c : O', Θ (MvPowerSeries.C c) = κ c)
    (hΘT : Θ (axisT O') = completedPointMap
      (BlowupChart (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F)) P
      (chartBase (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F)
      (surfaceMk O pi u a b E)))
    (hΘX : Θ (axisX O') = completedPointMap
      (BlowupChart (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F)) P
      (chartSlope (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F))
      - κ α) :
    Θ.comp s =
      (completedPointMap
        (BlowupChart (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F))
        P).comp ((chartBase (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E)
        (surfaceMk O pi u a b F)).comp (surfaceMk O pi u a b)) := by sorry
