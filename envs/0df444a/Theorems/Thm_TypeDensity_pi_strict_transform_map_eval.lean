-- Prove2me | Theorems.Thm_TypeDensity_pi_strict_transform_map_eval
-- name    : TypeDensity.pi_strict_transform_map_eval
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:04.049145+00:00
-- url     : https://prove2.me/theorems/b2eda144-e697-40d3-83e4-d8452789551e
-- title:
--   Over a finite product `Π C_j`, principal ideals and strict transforms are computed componentwise.
-- statement:
--   Over a finite product `Π C_j`, principal ideals and strict transforms are computed componentwise.
-- source:
--   TypeDensity/Measure/Atlas.lean#L40-L69

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
import Theorems.Thm_TypeDensity_principal_ideal_image
import Theorems.Thm_TypeDensity_pi_ideal_mem_iff_map_eval
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

theorem TypeDensity.pi_strict_transform_map_eval (O : Type) [CommRing O] (R : Type) [CommRing R] [Algebra O R]
    (ι : Type) [Finite ι] (C : ι → Type) [∀ j, CommRing (C j)] [∀ j, Algebra O (C j)]
    (alpha : ∀ j, R →ₐ[O] C j) (e g : ∀ j, C j) (d : ℕ) (J : Ideal R) :
    (∀ x : ∀ j, C j, x ∈ Ideal.span {g} ↔ ∀ j, x j ∈ Ideal.span {g j}) ∧
      (∀ j, (Ideal.span {g}).map (Pi.evalRingHom C j) = Ideal.span {g j}) ∧
      (∀ x : ∀ j, C j, x ∈ strictTransformIdeal (AlgHom.pi alpha) e d J ↔ ∀ j,
      x j ∈ strictTransformIdeal (alpha j) (e j) d J) ∧ ∀ j,
      (strictTransformIdeal (AlgHom.pi alpha) e d J).map (Pi.evalRingHom C j) =
      strictTransformIdeal (alpha j) (e j) d J := by sorry
