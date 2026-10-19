-- Prove2me | Theorems.Thm_TypeDensity_actual_finite_cech_coefficient_length
-- name    : TypeDensity.actual_finite_cech_coefficient_length
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:14:50.395239+00:00
-- url     : https://prove2.me/theorems/9d69f0c3-3624-4df1-975e-0e46263b083b
-- title:
--   The length of the cokernel of the twisted finite Čech differential at level `n` is `∑_{j < n} (d - j - 1)`.
-- statement:
--   The length of the cokernel of the twisted finite Čech differential at level `n` is `∑_{j < n} (d - j - 1)`.
-- source:
--   TypeDensity/Blowup/CechStability.lean#L80-L122

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
import Theorems.Thm_TypeDensity_actual_cech_differentials_commute_with_reduction
import Theorems.Thm_TypeDensity_actual_cech_reductions_surjective
import Theorems.Thm_TypeDensity_actual_negative_layer_coker_exact
import Theorems.Thm_TypeDensity_two_term_coker_map_surjective
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

theorem TypeDensity.actual_finite_cech_coefficient_length (O R : Type) [CommRing O] [CommRing R] [Algebra O R]
    (t x : R) (hreg : RegularParameterPair R t x) (beta : BlowupRestriction R t x)
    (hregSwap : RegularParameterPair R x t) [(Ideal.span ({t,x} : Set R)).IsMaximal]
    (hres : Function.Surjective (algebraMap O (R ⧸ Ideal.span {t,x}))) (d n : ℕ)
    (hpres : ∀ j : ℕ, cechInputLattice R t x j ≤
      (cechOutputLattice R t x j).comap (fullCechDifferential R t x beta d)) :
    Module.length O
      (CechLevelOutput R t x n ⧸ LinearMap.range (finiteCechDifferential R t x beta d n (hpres n)))
      = ((∑ j ∈ Finset.range n, (d-j-1) : ℕ) : ℕ∞) := by sorry
