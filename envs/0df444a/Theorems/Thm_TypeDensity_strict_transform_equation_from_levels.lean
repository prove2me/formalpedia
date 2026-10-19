-- Prove2me | Theorems.Thm_TypeDensity_strict_transform_equation_from_levels
-- name    : TypeDensity.strict_transform_equation_from_levels
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:30:35.57746+00:00
-- url     : https://prove2.me/theorems/fdfb900b-0388-49ca-b17b-e93905903d84
-- title:
--   Recovering a strict transform equation from its truncations: if `φ ≡ e ^ d * F j` modulo `e ^ j` and `(F j, e ^ j) = (g, e ^ j)` for all `j`, then `φ = e ^ d * g * v` for a unit `v`.
-- statement:
--   Recovering a strict transform equation from its truncations: if `φ ≡ e ^ d * F j` modulo `e ^ j` and `(F j, e ^ j) = (g, e ^ j)` for all `j`, then `φ = e ^ d * g * v` for a unit `v`.
-- source:
--   TypeDensity/Blowup/StrictNormalizer.lean#L1364-L1432

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

theorem TypeDensity.strict_transform_equation_from_levels (S : Type) [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] (e g : S) (he : e ∈ IsLocalRing.maximalIdeal S)
    (hereg : Function.Injective (fun a : S => e * a))
    (hg : Function.Injective
    (fun a : S ⧸ Ideal.span {e} => Ideal.Quotient.mk (Ideal.span {e}) g * a)) (d : ℕ) (F : ℕ → S)
    (hFideal : ∀ j : ℕ, Ideal.span {F j, e^j} = Ideal.span {g, e^j}) (φ : S)
    (hφ : ∀ j : ℕ, φ - e^d * F j ∈ Ideal.span {e^j}) :
    ∃ v : Sˣ, φ = e^d * g * (v : S) := by sorry
