-- Prove2me | Theorems.Thm_TypeDensity_finite_support_generators_compatible
-- name    : TypeDensity.finite_support_generators_compatible
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:32:40.286165+00:00
-- url     : https://prove2.me/theorems/6edb0d98-d84a-4c3e-8c27-54306a916f2e
-- title:
--   Generators of consecutive level kernels generate the same ideal modulo `(e)^j`.
-- statement:
--   Generators of consecutive level kernels generate the same ideal modulo `(e)^j`.
-- source:
--   TypeDensity/Blowup/CurveOrders.lean#L847-L860

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

theorem TypeDensity.finite_support_generators_compatible (A : Type) [CommRing A] [IsNoetherianRing A] (ι : Type)
    [Finite ι] (P : ι → Ideal A) [∀ i, (P i).IsMaximal] (hP : Function.Injective P) (e : A)
    (g : ∀ i, CompletedLocalAt A (P i)) (L : ι → ℕ) (hfin : ∀ i,
    ((IsLocalRing.maximalIdeal (Localization.AtPrime (P i))).map
    (localCompletionMap (Localization.AtPrime (P i)))) ^ (L i) ≤
      finiteLocalCurveIdeal A (P i) e (g i) 1) (F : ℕ → A)
    (hF : ∀ j : ℕ, finiteSupportLevelKernel A ι P
    (fun i => finiteLocalCurveIdeal A (P i) e (g i) j) e j = Ideal.span
    {Ideal.Quotient.mk ((Ideal.span {e})^j) (F j)}) (j : ℕ) :
    Ideal.span {Ideal.Quotient.mk ((Ideal.span {e})^j) (F (j+1))} = Ideal.span
        {Ideal.Quotient.mk ((Ideal.span {e})^j) (F j)} := by sorry
