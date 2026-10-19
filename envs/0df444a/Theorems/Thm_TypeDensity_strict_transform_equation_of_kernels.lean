-- Prove2me | Theorems.Thm_TypeDensity_strict_transform_equation_of_kernels
-- name    : TypeDensity.strict_transform_equation_of_kernels
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:32:46.635034+00:00
-- url     : https://prove2.me/theorems/b97eec7d-cadf-463d-9aff-c8d627fe93a3
-- title:
--   Chart-independent form of the strict-transform equation: let `P` be finitely many distinct maximal ideals of a noetherian ring `A` containing `z`, with local equations `g` of finite contact with `z`,
-- statement:
--   Chart-independent form of the strict-transform equation: let `P` be finitely many distinct maximal ideals of a noetherian ring `A` containing `z`, with local equations `g` of finite contact with `z`, and let `F` be generators of the level kernels, `(F j) + (z)^j = ⋂ (g, z^j)`. If `y ≡ z^d F j mod z^j` for every `j` and `z`, `g` form a regular sequence in `(A_P)^`, then `y = z^d · g · unit` in `(A_P)^`.
-- source:
--   TypeDensity/Blowup/CurveSections.lean#L951-L991

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
import Theorems.Thm_TypeDensity_finite_support_completion_recovers
import Theorems.Thm_TypeDensity_strict_transform_equation_from_levels
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

theorem TypeDensity.strict_transform_equation_of_kernels {A ι : Type} [CommRing A] [IsNoetherianRing A]
    [Finite ι] (P : ι → Ideal A) [∀ s, (P s).IsMaximal] (hP : Function.Injective P) (z : A)
    (hz : ∀ s, z ∈ P s) (g : ∀ s, CompletedLocalAt A (P s))
    (hfin : ∀ j s, ∃ L, ((IsLocalRing.maximalIdeal (Localization.AtPrime (P s))).map
      (localCompletionMap _)) ^ L ≤ finiteLocalCurveIdeal A (P s) z (g s) j)
    (F : ℕ → A) (hF : ∀ j, Ideal.span {F j} ⊔ Ideal.span {z} ^ j =
      finiteSupportKernel A ι P (fun s => finiteLocalCurveIdeal A (P s) z (g s) j))
    (d : ℕ) (y : A) (hy : ∀ j, y - z ^ d * F j ∈ Ideal.span {z} ^ j) (s : ι)
    [IsNoetherianRing (CompletedLocalAt A (P s))]
    (hereg : Function.Injective
      (fun a : CompletedLocalAt A (P s) => completedPointMap A (P s) z * a))
    (hgreg : Function.Injective (fun a : CompletedLocalAt A (P s) ⧸
      Ideal.span {completedPointMap A (P s) z} =>
      Ideal.Quotient.mk (Ideal.span {completedPointMap A (P s) z}) (g s) * a)) :
    ∃ v : (CompletedLocalAt A (P s))ˣ, completedPointMap A (P s) y =
      completedPointMap A (P s) z ^ d * g s * (v : CompletedLocalAt A (P s)) := by sorry
