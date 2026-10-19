-- Prove2me | Theorems.Thm_TypeDensity_coordinate_remainder_raises_order
-- name    : TypeDensity.coordinate_remainder_raises_order
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:40.53786+00:00
-- url     : https://prove2.me/theorems/7a470306-d1d5-4b63-b285-ba94eade7576
-- title:
--   The coordinate remainder `(z, v) ↦ π • E (v ∑ zᵢ bᵢ)` raises `π`-adic order.
-- statement:
--   The coordinate remainder `(z, v) ↦ π • E (v ∑ zᵢ bᵢ)` raises `π`-adic order.
-- source:
--   TypeDensity/Measure/AdicCylinders.lean#L661-L693

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

theorem TypeDensity.coordinate_remainder_raises_order (O R : Type) [CommRing O] [CommRing R] [Algebra O R]
    (n : ℕ) (pi : O) (b : Fin n → R) (E : R ≃ₗ[O] ((Fin n → O) × R)) :
    RaisesAdicOrder (Ideal.span {pi}) (coordinateRemainder pi b E) := by sorry
