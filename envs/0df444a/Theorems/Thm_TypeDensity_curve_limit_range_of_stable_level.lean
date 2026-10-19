-- Prove2me | Theorems.Thm_TypeDensity_curve_limit_range_of_stable_level
-- name    : TypeDensity.curve_limit_range_of_stable_level
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:14:56.279969+00:00
-- url     : https://prove2.me/theorems/9c6b1f09-0124-490c-b774-830ca7412a72
-- title:
--   Let `σ` be a section of the surface-to-curve-limit map that sends a surface function to its constant thread.
-- statement:
--   Let `σ` be a section of the surface-to-curve-limit map that sends a surface function to its constant thread. If a thread `p` of the curve order limit agrees with a surface function modulo the curve lattice at a single stable level `J ≥ d - 1`, then its class lies in the range of `σ`.
-- source:
--   TypeDensity/Blowup/CechStability.lean#L249-L310

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
import Theorems.Thm_TypeDensity_actual_twisted_coker_reduction_bijective
import Theorems.Thm_TypeDensity_actual_cech_preserves_exceptional_lattices
import Theorems.Thm_TypeDensity_actual_cech_differentials_commute_with_reduction
import Theorems.Thm_TypeDensity_curve_lattices_antitone
import Theorems.Thm_TypeDensity_surface_to_curve_quotient_kernel
import Theorems.Thm_TypeDensity_curve_section_connecting_class_zero_iff
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

theorem TypeDensity.curve_limit_range_of_stable_level (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (d : ℕ) (G : GluedGenerators R t x beta d)
    (hreg : RegularParameterPair R t x) (hregSwap : RegularParameterPair R x t)
    (hregF : ∀ j : ℕ, Function.Injective (fun c : BlowupOverlap R t x ⧸
      (Ideal.span {overlapException R t x})^j =>
      Ideal.Quotient.mk ((Ideal.span {overlapException R t x})^j)
      ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (G.left j)) * c))
    (f : R)
    (hf : ∀ j : ℕ, surfaceToCechInput R t x j f =
      (cechInputLattice R t x j).mkQ (gluedFunctionPair R t x G j))
    [IsAdicComplete (Ideal.span {t,x}) R] (J : ℕ) (hJ : d - 1 ≤ J)
    (σ : R →ₗ[R] CurveOrderLimit R t x beta G)
    (hσ : ∀ r : R, ∃ p : curveThreads R t x beta G, σ r = curveLimitMk R t x beta G p ∧ ∀ j : ℕ,
      p.val j = surfaceToChartPair R t x r)
    (p : curveThreads R t x beta G)
    (hp : ∃ r : R, p.val J - surfaceToChartPair R t x r ∈ curveIdealLattice R t x beta G J) :
    curveLimitMk R t x beta G p ∈ LinearMap.range σ := by sorry
