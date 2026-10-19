-- Prove2me | Theorems.Thm_TypeDensity_continuousOn_of_congruence_compatible
-- name    : TypeDensity.continuousOn_of_congruence_compatible
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:14.640563+00:00
-- url     : https://prove2.me/theorems/0b2f6422-7074-489e-a560-69e2ffbdca61
-- title:
--   A map between finite products of adic rings that preserves congruence modulo `I₁ ^ L` (sending it to congruence modulo `I₂ ^ L`) on a set `C` is continuous on `C`.
-- statement:
--   A map between finite products of adic rings that preserves congruence modulo `I₁ ^ L` (sending it to congruence modulo `I₂ ^ L`) on a set `C` is continuous on `C`.
-- source:
--   TypeDensity/Formula/PatternCounts.lean#L626-L659

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Formula_FiniteFieldCounts
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Formula_PatternCounts
import Theorems.Thm_TypeDensity_coordinate_cylinder_clopen
import Theorems.Thm_TypeDensity_finite_coordinate_adic_congruence
import Theorems.Thm_TypeDensity_finite_coordinate_cylinder_basis
import Theorems.Thm_TypeDensity_adic_congruence_rules
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PicardGroup
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.continuousOn_of_congruence_compatible (O₁ O₂ : Type) [CommRing O₁] [TopologicalSpace O₁]
    [IsTopologicalRing O₁] (I₁ : Ideal O₁) (h₁ : IsAdic I₁) [CommRing O₂] [TopologicalSpace O₂]
    [IsTopologicalRing O₂] (I₂ : Ideal O₂) (h₂ : IsAdic I₂) (ι : Type) [Finite ι] (d : ι → ℕ)
    (n₂ : ℕ) (C : Set (∀ i, Fin (d i) → O₁)) (f : (∀ i, Fin (d i) → O₁) → (Fin n₂ → O₂))
    (hf : ∀ (L : ℕ), ∀ a ∈ C, ∀ a' ∈ C, (∀ i j, a i j - a' i j ∈ I₁ ^ L) →
      ∀ j, f a j - f a' j ∈ I₂ ^ L) :
    ContinuousOn f C := by sorry
