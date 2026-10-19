-- Prove2me | Theorems.Thm_TypeDensity_common_vertical_exponent
-- name    : TypeDensity.common_vertical_exponent
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:48.323506+00:00
-- url     : https://prove2.me/theorems/96b9ee9d-32f3-4f89-a562-655683ae2dd4
-- title:
--   If each component `e j` divides a power of `π` up to `d`-th powers, then a single exponent `s ≥ s₀` works for all components of the finite product simultaneously.
-- statement:
--   If each component `e j` divides a power of `π` up to `d`-th powers, then a single exponent `s ≥ s₀` works for all components of the finite product simultaneously.
-- source:
--   TypeDensity/Measure/AdicCylinders.lean#L533-L548

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.MvPolynomial
set_option autoImplicit false

open TypeDensity
open MeasureTheory
open scoped BigOperators ENNReal

theorem TypeDensity.common_vertical_exponent (O : Type) [CommRing O] (ι : Type) [Finite ι] (C : ι → Type)
    [∀ j, CommRing (C j)] [∀ j, Algebra O (C j)] (pi : O) (e : ∀ j, C j) (d : ℕ)
    (hvert : ∀ j, ∃ (s : ℕ) (cj : C j), algebraMap O (C j) pi ^ s = e j ^ d * cj) (s₀ : ℕ) :
    ∃ (s : ℕ) (cc : ∀ j, C j), s₀ ≤ s ∧ (algebraMap O (∀ j, C j) pi) ^ s = e ^ d * cc := by sorry
