-- Prove2me | Theorems.Thm_TypeDensity_finite_support_kernel_localize
-- name    : TypeDensity.finite_support_kernel_localize
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:31.358006+00:00
-- url     : https://prove2.me/theorems/600ba890-6c46-47cd-acc3-696a97889206
-- title:
--   Localizing a finite-support kernel: the extension to `S` of the finite-support kernel is the infimum, over the points `i` that survive in `S`, of the transported completed ideals, the other points col
-- statement:
--   Localizing a finite-support kernel: the extension to `S` of the finite-support kernel is the infimum, over the points `i` that survive in `S`, of the transported completed ideals, the other points collapsing to the unit ideal.
-- source:
--   TypeDensity/Blowup/PointTransport.lean#L217-L252

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
import Theorems.Thm_TypeDensity_contracted_ideal_map_localization_top
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
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.finite_support_kernel_localize (A S : Type) [CommRing A] [CommRing S] [Algebra A S]
    (M : Submonoid A) [IsLocalization M S] (ι : Type) [Finite ι] (P : ι → Ideal A)
    [∀ i, (P i).IsPrime] (J : ∀ i, Ideal (CompletedLocalAt A (P i))) (σ : ι → Prop)
    (T : ι → Type) [∀ i, CommRing (T i)] (ψ : ∀ i, S →+* T i)
    (Φ : ∀ i, CompletedLocalAt A (P i) ≃+* T i)
    (hΦ : ∀ i, σ i → ∀ a : A, Φ i (completedPointMap A (P i) a) = ψ i (algebraMap A S a))
    (hcollapse : ∀ i, ¬ σ i → ∃ m ∈ M, m ∈ P i) (L : ι → ℕ)
    (hL : ∀ i, (P i)^(L i) ≤ (J i).comap (completedPointMap A (P i))) :
    (finiteSupportKernel A ι P J).map (algebraMap A S) = ⨅ i : {i // σ i},
    ((J i.val).map (Φ i.val)).comap (ψ i.val) := by sorry
