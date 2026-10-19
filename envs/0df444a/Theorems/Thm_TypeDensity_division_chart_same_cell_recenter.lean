-- Prove2me | Theorems.Thm_TypeDensity_division_chart_same_cell_recenter
-- name    : TypeDensity.division_chart_same_cell_recenter
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:51.09998+00:00
-- url     : https://prove2.me/theorems/04187670-ca55-49b5-88ce-6f48cfb76c1f
-- title:
--   Recentring for two division charts of the same rank whose centres generate the same ideal modulo `π` (see `division_data_same_cell_recenter`).
-- statement:
--   Two division charts of the same rank whose centres generate the same ideal modulo `π` can be recentred (see `division_data_same_cell_recenter`).
-- source:
--   TypeDensity/Measure/AdicCylinders.lean#L880-L893

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Theorems.Thm_TypeDensity_division_data_same_cell_recenter
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

theorem TypeDensity.division_chart_same_cell_recenter (O R : Type) [CommRing O] [CommRing R] [Algebra O R]
    [IsLocalRing R] (pi : O) (hpm : algebraMap O R pi ∈ IsLocalRing.maximalIdeal R) (n : ℕ)
    (f g : R) (b c : Fin n → R) (hb : IsDivisionChart O R pi f b) (hc : IsDivisionChart O R pi g c)
    (hres : Ideal.span {Ideal.Quotient.mk (Ideal.span {algebraMap O R pi}) f} =
      Ideal.span {Ideal.Quotient.mk (Ideal.span {algebraMap O R pi}) g}) :
    ∃ (g' : R) (c' : Fin n → R) (F : R ≃ₗ[O] ((Fin n → O) × R)) (h₀ : R),
      (∀ s, F.symm s = divisionMap g' c' s) ∧ f = g' + pi • h₀ ∧
      Function.Injective (fun y : R ⧸ Ideal.span {algebraMap O R pi} =>
        y * Ideal.Quotient.mk (Ideal.span {algebraMap O R pi}) g') ∧
      ∀ z : Fin n → O, coordinateIdeal pi g c z = coordinateIdeal pi g' c' z := by sorry
