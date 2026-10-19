-- Prove2me | Theorems.Thm_TypeDensity_two_le_ringKrullDim_of_regular_pair
-- name    : TypeDensity.two_le_ringKrullDim_of_regular_pair
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:32:14.000329+00:00
-- url     : https://prove2.me/theorems/6b59dc74-6384-4016-bab0-c7b0a9869521
-- title:
--   A regular sequence `t, x` with `R/(t, x)` nontrivial forces `2 ≤ dim R`.
-- statement:
--   A regular sequence `t, x` with `R/(t, x)` nontrivial forces `2 ≤ dim R`.
-- source:
--   TypeDensity/Surfaces/Regularity.lean#L312-L341

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Blowup_Charts
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PicardGroup
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.two_le_ringKrullDim_of_regular_pair {R : Type} [CommRing R] (t x : R)
    (h1 : Function.Injective (fun a : R ↦ t*a))
    (h2 : Function.Injective
        (fun a : R ⧸ Ideal.span {t} ↦ Ideal.Quotient.mk (Ideal.span {t}) x * a))
    (hP : Nontrivial (R ⧸ Ideal.span {t, x})) :
    (2 : WithBot ℕ∞) ≤ ringKrullDim R := by sorry
