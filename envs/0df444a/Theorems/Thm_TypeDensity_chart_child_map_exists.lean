-- Prove2me | Theorems.Thm_TypeDensity_chart_child_map_exists
-- name    : TypeDensity.chart_child_map_exists
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:09.662722+00:00
-- url     : https://prove2.me/theorems/3bb7a502-894e-4a02-8d3f-01899309144f
-- title:
--   A substitution `s : O[[T,X]] → O'[[T,X]]` with `E ↦ T`, `F ↦ T (X + α)` that maps the relation of `R` into the relation ideal of `R'` induces a chart map `R[f/e] → R'` with `f/e ↦ x' + α`.
-- statement:
--   A substitution `s : O[[T,X]] → O'[[T,X]]` with `E ↦ T`, `F ↦ T (X + α)` that maps the relation of `R` into the relation ideal of `R'` induces a chart map `R[f/e] → R'` with `f/e ↦ x' + α`.
-- source:
--   TypeDensity/Surfaces/ChartCompletions.lean#L206-L237

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
import Theorems.Thm_TypeDensity_blowup_chart_universal
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

theorem TypeDensity.chart_child_map_exists (O O' : Type) [CommRing O] [CommRing O'] (pi : O)
    (u : (TwoSeries O)ˣ) (a b : ℕ) (pi' : O') (u' : (TwoSeries O')ˣ) (a' b' : ℕ) (E F : TwoSeries O)
    (s : TwoSeries O →+* TwoSeries O')
    (hs : s (surfaceRelation O pi u a b) ∈ surfaceIdeal O' pi' u' a' b') (α : O')
    (hE : s E = axisT O') (hF : s F = axisT O' * (axisX O' + MvPowerSeries.C α)) :
    ∃ Λ : (BlowupChart (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F)) →+* ConcreteSurface O' pi' u' a' b',
      (∀ g : TwoSeries O, Λ ((chartBase (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F)) (surfaceMk O pi u a b g)) =
          surfaceMk O' pi' u' a' b' (s g)) ∧
      Λ ((chartSlope (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F))) = surfaceX O' pi' u' a' b' + algebraMap O'
          (ConcreteSurface O' pi' u' a' b') α := by sorry
