-- Prove2me | Theorems.Thm_TypeDensity_division_data_same_cell_recenter
-- name    : TypeDensity.division_data_same_cell_recenter
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:41.644554+00:00
-- url     : https://prove2.me/theorems/7058429d-7f5d-44a7-80eb-a54787551383
-- title:
--   Recentring: if the regular element `f` and the chart centre `g` (with division equivalence `Ec`) generate the same ideal modulo `π`, then the chart can be rescaled by a unit so that its new centre `g'
-- statement:
--   Recentring: if the regular element `f` and the chart centre `g` (with division equivalence `Ec`) generate the same ideal modulo `π`, then the chart can be rescaled by a unit so that its new centre `g'` satisfies `f = g' + π h₀`, with the same curve ideals.
-- source:
--   TypeDensity/Measure/AdicCylinders.lean#L821-L878

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

theorem TypeDensity.division_data_same_cell_recenter (O R : Type) [CommRing O] [CommRing R] [Algebra O R]
    [IsLocalRing R] (pi : O) (hpm : algebraMap O R pi ∈ IsLocalRing.maximalIdeal R) (n : ℕ)
    (f g : R) (c : Fin n → R)
    (hf : Function.Injective (fun y : R ⧸ Ideal.span {algebraMap O R pi} =>
      y * Ideal.Quotient.mk (Ideal.span {algebraMap O R pi}) f))
    (Ec : R ≃ₗ[O] ((Fin n → O) × R)) (hEc : ∀ s, Ec.symm s = divisionMap g c s)
    (hres : Ideal.span {Ideal.Quotient.mk (Ideal.span {algebraMap O R pi}) f} =
      Ideal.span {Ideal.Quotient.mk (Ideal.span {algebraMap O R pi}) g}) :
    ∃ (g' : R) (c' : Fin n → R) (F : R ≃ₗ[O] ((Fin n → O) × R)) (h₀ : R),
      (∀ s, F.symm s = divisionMap g' c' s) ∧ f = g' + pi • h₀ ∧
      Function.Injective (fun y : R ⧸ Ideal.span {algebraMap O R pi} =>
        y * Ideal.Quotient.mk (Ideal.span {algebraMap O R pi}) g') ∧
      ∀ z : Fin n → O, coordinateIdeal pi g c z = coordinateIdeal pi g' c' z := by sorry
