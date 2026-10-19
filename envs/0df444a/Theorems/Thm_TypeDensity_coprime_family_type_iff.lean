-- Prove2me | Theorems.Thm_TypeDensity_coprime_family_type_iff
-- name    : TypeDensity.coprime_family_type_iff
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:18.176999+00:00
-- url     : https://prove2.me/theorems/50b31cb0-0dba-4ca1-8357-6a638974fd79
-- title:
--   For a finite family of monic, pairwise coprime polynomials, the product has type `σ` exactly when `σ` is the sum of types of the factors.
-- statement:
--   For a finite family of monic, pairwise coprime polynomials, the product has type `σ` exactly when `σ` is the sum of types of the factors.
-- source:
--   TypeDensity/Formula/TypeTransport.lean#L58-L78

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
import Theorems.Thm_TypeDensity_polynomial_type_dvd
import Theorems.Thm_TypeDensity_polynomial_type_mul_coprime
import Theorems.Thm_TypeDensity_polynomial_type_unique
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

theorem TypeDensity.coprime_family_type_iff (O : Type) [CommRing O] [IsDomain O] (ι : Type) [Fintype ι]
    (F : ι → Polynomial (BaseField O)) (hF : ∀ i, (F i).Monic)
    (hc : ∀ i j, i ≠ j → IsCoprime (F i) (F j)) (σ : FactorType) :
    HasPolynomialTypeF O (∏ i, F i) σ ↔
      ∃ τ : ι → FactorType, (∀ i, HasPolynomialTypeF O (F i) (τ i)) ∧ σ = ∑ i, τ i := by sorry
