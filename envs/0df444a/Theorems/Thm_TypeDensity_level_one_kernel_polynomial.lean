-- Prove2me | Theorems.Thm_TypeDensity_level_one_kernel_polynomial
-- name    : TypeDensity.level_one_kernel_polynomial
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:56.074524+00:00
-- url     : https://prove2.me/theorems/f767fcb4-198d-4b0d-9682-36c6f04300c6
-- title:
--   **Level-one kernels on a blow-up chart.** Let `e` identify the exceptional line of the chart `R[x/t]` with `k[X]` (`k = R ⧸ I`, `I = (t, x)`), and let `P s` be finitely many distinct closed points of
-- statement:
--   **Level-one kernels on a blow-up chart.** Let `e` identify the exceptional line of the chart `R[x/t]` with `k[X]` (`k = R ⧸ I`, `I = (t, x)`), and let `P s` be finitely many distinct closed points of the exceptional line carrying finite-length level-one curve data `g s`. Then the points correspond to distinct monic irreducibles `φ s` (with `φ s = X` exactly at the points where the slope vanishes, and `deg φ s` the residue degree), the level-one lengths are finite numbers `m s`, and the intersection of the contracted level-one ideals maps to `(∏ φ s ^ m s)`.
-- source:
--   TypeDensity/Blowup/DivisorPoints.lean#L808-L889

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
import Definitions.Def_TypeDensity_Surfaces_ConcreteAtlas
import Definitions.Def_TypeDensity_Blowup_DivisorPoints
import Theorems.Thm_TypeDensity_completed_point_power_contraction
import Theorems.Thm_TypeDensity_blowup_chart_exceptional_point_polynomial
import Theorems.Thm_TypeDensity_pairwise_distinct_irreducible_pow_iInf
import Theorems.Thm_TypeDensity_polynomial_ideal_of_irreducible_pow_le
import Theorems.Thm_TypeDensity_polynomial_quotient_irreducible_pow_length
import Theorems.Thm_TypeDensity_quotient_ring_length_intrinsic
import Theorems.Thm_TypeDensity_finite_completed_point_quotient_surjective
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

theorem TypeDensity.level_one_kernel_polynomial (R : Type) [CommRing R] (t x : R) (I : Ideal R) [I.IsMaximal]
    (hI : Ideal.span ({t,x} : Set R) = I) [IsNoetherianRing (BlowupChart R t x)]
    (e : (BlowupChart R t x ⧸ chartExceptional R t x) ≃+* Polynomial (R ⧸ I))
    (he : ∀ r : R, e (Ideal.Quotient.mk (chartExceptional R t x) (chartBase R t x r)) =
      Polynomial.C (Ideal.Quotient.mk I r))
    (heZ : e (Ideal.Quotient.mk (chartExceptional R t x) (chartSlope R t x)) = Polynomial.X)
    {ι : Type} [Finite ι] (P : ι → Ideal (BlowupChart R t x)) [∀ s, (P s).IsMaximal]
    (hinjP : Function.Injective P) (htP : ∀ s, chartBase R t x t ∈ P s)
    (g : ∀ s, CompletedLocalAt (BlowupChart R t x) (P s))
    (hfin : ∀ s, ∃ L : ℕ, ((IsLocalRing.maximalIdeal (Localization.AtPrime (P s))).map
      (localCompletionMap (Localization.AtPrime (P s))))^L ≤
      finiteLocalCurveIdeal (BlowupChart R t x) (P s) (chartBase R t x t) (g s) 1) :
    ∃ (φ : ι → Polynomial (R ⧸ I)) (m : ι → ℕ), (∀ s, (φ s).Monic ∧ Irreducible (φ s)) ∧
      Function.Injective φ ∧ (∀ s, chartSlope R t x ∈ P s ↔ φ s = Polynomial.X) ∧
      (∀ s, Module.length R (BlowupChart R t x ⧸ P s) = ((φ s).natDegree : ℕ∞)) ∧
      (∀ s, Module.length (CompletedLocalAt (BlowupChart R t x) (P s))
        (CompletedLocalAt (BlowupChart R t x) (P s) ⧸
          finiteLocalCurveIdeal (BlowupChart R t x) (P s) (chartBase R t x t) (g s) 1) =
        (m s : ℕ∞)) ∧
      ((⨅ s, contractedLocalCurveIdeal (BlowupChart R t x) (P s) (chartBase R t x t) (g s) 1).map
        (Ideal.Quotient.mk (chartExceptional R t x))).map e = Ideal.span {∏ᶠ s, φ s ^ m s} := by sorry
