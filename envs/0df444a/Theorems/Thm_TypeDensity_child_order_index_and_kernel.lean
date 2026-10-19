-- Prove2me | Theorems.Thm_TypeDensity_child_order_index_and_kernel
-- name    : TypeDensity.child_order_index_and_kernel
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:32:10.094979+00:00
-- url     : https://prove2.me/theorems/55338aec-35ca-4da5-8186-6f01f8258f94
-- title:
--   The child-order map has kernel `(f)` and cokernel of length `binom(d, 2)`.
-- statement:
--   The child-order map has kernel `(f)` and cokernel of length `binom(d, 2)`.
-- source:
--   TypeDensity/Measure/MemberCharts.lean#L483-L524

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
import Definitions.Def_TypeDensity_Surfaces_TruncatedSeries
import Definitions.Def_TypeDensity_Blowup_TwoChartCurveData
import Definitions.Def_TypeDensity_Surfaces_ConcreteAtlas
import Definitions.Def_TypeDensity_Recursion_Members
import Definitions.Def_TypeDensity_Measure_MemberCharts
import Theorems.Thm_TypeDensity_actual_finite_cech_coefficient_triangular
import Theorems.Thm_TypeDensity_curve_limit_range_of_stable_level
import Theorems.Thm_TypeDensity_actual_cech_preserves_exceptional_lattices
import Theorems.Thm_TypeDensity_curve_limit_level_map_exists
import Theorems.Thm_TypeDensity_surface_to_curve_limit_kernel
import Theorems.Thm_TypeDensity_curve_limit_level_map_surjective
import Theorems.Thm_TypeDensity_curve_sections_connecting_map_exists
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
import Mathlib.Algebra.Group.NatPowAssoc
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal
variable (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (t x : R)
  (hreg : RegularParameterPair R t x) (beta : BlowupRestriction R t x)
  (hregSwap : RegularParameterPair R x t) [(Ideal.span ({t,x} : Set R)).IsMaximal]
  (hres : Function.Surjective (algebraMap O (R ⧸ Ideal.span {t,x})))
  [IsAdicComplete (Ideal.span {t,x}) R]
include hreg hregSwap hres

theorem TypeDensity.child_order_index_and_kernel [IsNoetherianRing (BlowupChart R t x)]
    [IsNoetherianRing (BlowupChart R x t)] (D : TwoChartCurveData R t x beta) (d : ℕ)
    (G : GluedGenerators R t x beta d)
    (hregF : ∀ j : ℕ, Function.Injective
      (fun c : BlowupOverlap R t x ⧸ (Ideal.span {overlapException R t x})^j =>
        Ideal.Quotient.mk ((Ideal.span {overlapException R t x})^j)
          ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (G.left j)) * c))
    (f : R)
    (hf : ∀ j : ℕ, surfaceToCechInput R t x j f =
      (cechInputLattice R t x j).mkQ (gluedFunctionPair R t x G j))
    (hclosed : (⨅ j : ℕ, (Ideal.span {f} ⊔ (Ideal.span {t,x})^j)) = Ideal.span {f})
    [∀ p : AllPoints D, IsLocalRing (localRing D p)]
    [∀ p : AllPoints D, IsNoetherianRing (localRing D p)]
    [∀ p : AllPoints D, IsAdicComplete (IsLocalRing.maximalIdeal (localRing D p)) (localRing D p)]
    [∀ p : AllPoints D, Algebra O (localRing D p)]
    (E : CurveOrderLimit R t x beta G ≃ₗ[O] childOrder D) (σ : R →ₗ[R] CurveOrderLimit R t x beta G)
    (hσ : ∀ r : R, ∃ p : curveThreads R t x beta G, σ r = curveLimitMk R t x beta G p ∧ ∀ j : ℕ,
      p.val j = surfaceToChartPair R t x r)
    (hE : ∀ (p : curveThreads R t x beta G) (r : R),
      (∀ j : ℕ, p.val j = surfaceToChartPair R t x r) → E (curveLimitMk R t x beta G p) =
      childOrderMap D r)
    (φ : R →ₗ[O] childOrder D) (hφ : ∀ r : R, φ r = childOrderMap D r) :
    RingHom.ker (childOrderMap D) = Ideal.span {f} ∧
      Module.length O ((childOrder D) ⧸ LinearMap.range φ) = (chooseTwo d : ℕ∞) := by sorry
