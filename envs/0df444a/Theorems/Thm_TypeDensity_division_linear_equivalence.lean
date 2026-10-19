-- Prove2me | Theorems.Thm_TypeDensity_division_linear_equivalence
-- name    : TypeDensity.division_linear_equivalence
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:45.555861+00:00
-- url     : https://prove2.me/theorems/bd1cc676-ef38-40fe-8ead-84d70c27ad30
-- title:
--   If `b` lifts an `O`-basis of `R/(f)` with `f ≠ 0` in a domain, the division map is the inverse of an `O`-linear equivalence `R ≃ O^n × R`.
-- statement:
--   If `b` lifts an `O`-basis of `R/(f)` with `f ≠ 0` in a domain, the division map is the inverse of an `O`-linear equivalence `R ≃ O^n × R`.
-- source:
--   TypeDensity/Measure/AdicCylinders.lean#L895-L914

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

theorem TypeDensity.division_linear_equivalence (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (n : ℕ)
    (f : R) (B : Module.Basis (Fin n) O (R ⧸ Ideal.span {f})) (b : Fin n → R)
    (hb : ∀ i, Ideal.Quotient.mk (Ideal.span {f}) (b i) = B i) [IsDomain R] (hf : f ≠ 0) :
    ∃ E : R ≃ₗ[O] ((Fin n → O) × R), ∀ s, E.symm s = divisionMap f b s := by sorry
