-- Prove2me | Theorems.Thm_TypeDensity_card_truncIndex_axis_segment
-- name    : TypeDensity.card_truncIndex_axis_segment
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:48.988425+00:00
-- url     : https://prove2.me/theorems/c2854ab5-bd70-45ea-a7b6-6b372c96ea82
-- title:
--   An initial segment `{e 0, …, e (c - 1)}` of an axis `f = 0` (parametrized by `g`) inside `truncIndex a b L` has `c` elements.
-- statement:
--   An initial segment `{e 0, …, e (c - 1)}` of an axis `f = 0` (parametrized by `g`) inside `truncIndex a b L` has `c` elements.
-- source:
--   TypeDensity/Surfaces/TruncatedSeries.lean#L189-L205

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
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
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.card_truncIndex_axis_segment (a b L c : ℕ) (f g : ℕ × ℕ → ℕ) (e : ℕ → ℕ × ℕ)
    (hfe : ∀ j, f (e j) = 0 ∧ g (e j) = j) (hef : ∀ x, f x = 0 → e (g x) = x)
    (hmem : ∀ j < c, e j ∈ truncIndex a b L) :
    (Finset.univ.filter fun s : truncIndex a b L => f s.1 = 0 ∧ g s.1 < c).card = c := by sorry
