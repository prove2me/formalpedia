-- Prove2me | Theorems.Thm_TypeDensity_chart_point_isMaximal_of_residue_surjective
-- name    : TypeDensity.chart_point_isMaximal_of_residue_surjective
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:30:22.143961+00:00
-- url     : https://prove2.me/theorems/4c92b0d4-2ccf-4bdc-b369-2655b1ecc04a
-- title:
--   The pullback of the maximal ideal of a local ring `S` along `Λ : A → S` is maximal when `Λ` is surjective modulo the maximal ideal.
-- statement:
--   The pullback of the maximal ideal of a local ring `S` along `Λ : A → S` is maximal when `Λ` is surjective modulo the maximal ideal.
-- source:
--   TypeDensity/Surfaces/Lengths.lean#L701-L714

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
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
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.chart_point_isMaximal_of_residue_surjective (A S : Type) [CommRing A] [CommRing S]
    [IsLocalRing S] (Λ : A →+* S) (hsurj : ∀ y : S, ∃ x : A, Λ x - y ∈ IsLocalRing.maximalIdeal S) :
    ((IsLocalRing.maximalIdeal S).comap Λ).IsMaximal := by sorry
