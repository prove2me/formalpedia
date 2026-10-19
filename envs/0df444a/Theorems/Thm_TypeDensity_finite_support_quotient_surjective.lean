-- Prove2me | Theorems.Thm_TypeDensity_finite_support_quotient_surjective
-- name    : TypeDensity.finite_support_quotient_surjective
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:33:10.219978+00:00
-- url     : https://prove2.me/theorems/c88f01aa-5556-44a5-890a-7eff5b29ad55
-- title:
--   The map from `A` to the product of finite-colength completed local quotients is surjective.
-- statement:
--   The map from `A` to the product of finite-colength completed local quotients is surjective.
-- source:
--   TypeDensity/Blowup/CurveOrders.lean#L769-L776

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
import Theorems.Thm_TypeDensity_finite_support_quotient_surjective_of_isPrime
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
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.finite_support_quotient_surjective (A : Type) [CommRing A] [IsNoetherianRing A] (ι : Type)
    [Finite ι] (P : ι → Ideal A) [∀ i, (P i).IsMaximal] (hP : Function.Injective P) (L : ι → ℕ)
    (J : ∀ i, Ideal (CompletedLocalAt A (P i))) (hJ : ∀ i,
    ((IsLocalRing.maximalIdeal (Localization.AtPrime (P i))).map
    (localCompletionMap (Localization.AtPrime (P i)))) ^ (L i) ≤ J i) :
    Function.Surjective (finiteSupportQuotientMap A ι P J) := by sorry
