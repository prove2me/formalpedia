-- Prove2me | Theorems.Thm_TypeDensity_chart_child_completion_map_exists
-- name    : TypeDensity.chart_child_completion_map_exists
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:53:14.438402+00:00
-- url     : https://prove2.me/theorems/5fdf8030-f25a-498b-8877-7cba9d031329
-- title:
--   A ring map `Λ : A → R'` to a concrete surface, under which `P` is the preimage of the parameter ideal, extends to the completed local ring of `A` at `P`.
-- statement:
--   A ring map `Λ : A → R'` to a concrete surface, under which `P` is the preimage of the parameter ideal, extends to the completed local ring of `A` at `P`.
-- source:
--   TypeDensity/Surfaces/Regularity.lean#L113-L173

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
import Theorems.Thm_TypeDensity_concrete_surface_isAdicComplete_maximalIdeal
import Theorems.Thm_TypeDensity_concrete_surface_maximalIdeal_eq
import Theorems.Thm_TypeDensity_concrete_surface_isLocalRing
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

theorem TypeDensity.chart_child_completion_map_exists (A : Type) [CommRing A] [IsNoetherianRing A] (O' : Type)
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] (pi' : O') (hpi' : Irreducible pi')
    (u' : (TwoSeries O')ˣ) (a' b' : ℕ) (ha' : 0 < a') (Λ : A →+* ConcreteSurface O' pi' u' a' b')
    (P : Ideal A) [P.IsPrime] (hP : ∀ x : A, x ∈ P ↔ Λ x ∈ surfaceParameterIdeal O' pi' u' a' b') :
    ∃ Λ' : CompletedLocalAt A P →+* ConcreteSurface O' pi' u' a' b', ∀ x : A,
      Λ' (completedPointMap A P x) = Λ x := by sorry
