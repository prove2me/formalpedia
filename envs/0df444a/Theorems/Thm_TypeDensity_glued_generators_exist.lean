-- Prove2me | Theorems.Thm_TypeDensity_glued_generators_exist
-- name    : TypeDensity.glued_generators_exist
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:52:49.237682+00:00
-- url     : https://prove2.me/theorems/cf706676-6b88-4271-bc5d-eafc4fb6eaba
-- title:
--   Compatible systems of chart generators `gA`, `gB` that are regular, agree on the overlap and are normalized at level one can be replaced by glued generators generating the same ideals at every level.
-- statement:
--   Compatible systems of chart generators `gA`, `gB` that are regular, agree on the overlap and are normalized at level one can be replaced by glued generators generating the same ideals at every level.
-- source:
--   TypeDensity/Blowup/CurveSections.lean#L772-L830

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
import Theorems.Thm_TypeDensity_glued_generators_level_one
import Theorems.Thm_TypeDensity_beta_right_chartBase_self
import Theorems.Thm_TypeDensity_two_chart_layer_correction_zpow
import Theorems.Thm_TypeDensity_transition_unit_congruent_one
import Theorems.Thm_TypeDensity_beta_right_chartBase
import Theorems.Thm_TypeDensity_principal_power_unit_lift
import Theorems.Thm_TypeDensity_regular_principal_generators_associated
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

theorem TypeDensity.glued_generators_exist (R : Type) [CommRing R] (t x : R) (beta : BlowupRestriction R t x)
    (hreg : RegularParameterPair R t x) (d : ℕ)
    (gA : ℕ → BlowupChart R t x) (gB : ℕ → BlowupChart R x t)
    (hA : ∀ j : ℕ, Ideal.span {Ideal.Quotient.mk ((chartExceptional R t x)^j) (gA (j+1))} =
      Ideal.span {Ideal.Quotient.mk ((chartExceptional R t x)^j) (gA j)})
    (hB : ∀ j : ℕ, Ideal.span {Ideal.Quotient.mk ((chartExceptional R x t)^j) (gB (j+1))} =
      Ideal.span {Ideal.Quotient.mk ((chartExceptional R x t)^j) (gB j)})
    (hregA : ∀ j : ℕ, Function.Injective (fun c : BlowupChart R t x ⧸ (chartExceptional R t x)^j =>
      Ideal.Quotient.mk ((chartExceptional R t x)^j) (gA j) * c))
    (hregBc : ∀ j : ℕ, Function.Injective (fun c : BlowupChart R x t ⧸ (chartExceptional R x t)^j =>
      Ideal.Quotient.mk ((chartExceptional R x t)^j) (gB j) * c))
    (hoverlap : ∀ j : ℕ, Ideal.span {Ideal.Quotient.mk ((Ideal.span {overlapException R t x})^j)
      ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (gA j))} =
      Ideal.span {Ideal.Quotient.mk ((Ideal.span {overlapException R t x})^j) (beta.right (gB j))})
    (hregC : ∀ j : ℕ, Function.Injective (fun c : BlowupOverlap R t x ⧸
      (Ideal.span {overlapException R t x})^j =>
      Ideal.Quotient.mk ((Ideal.span {overlapException R t x})^j) (beta.right (gB j)) * c))
    (hnorm : ∃ u : Rˣ, (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (gA 1) - algebraMap
      R (BlowupOverlap R t x) (u : R) * ((overlapSlope R t x)^d * beta.right (gB 1)) ∈
      (Ideal.span {overlapException R t x})) :
    ∃ G : GluedGenerators R t x beta d, ∀ j : ℕ,
      Ideal.span {Ideal.Quotient.mk ((chartExceptional R t x)^j) (G.left j)} =
      Ideal.span {Ideal.Quotient.mk ((chartExceptional R t x)^j) (gA j)} ∧
      Ideal.span {Ideal.Quotient.mk ((chartExceptional R x t)^j) (G.right j)} =
      Ideal.span {Ideal.Quotient.mk ((chartExceptional R x t)^j) (gB j)} := by sorry
