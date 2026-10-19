-- Prove2me | Theorems.Thm_TypeDensity_coordinate_ideal_in_residue_cell
-- name    : TypeDensity.coordinate_ideal_in_residue_cell
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:52.373475+00:00
-- url     : https://prove2.me/theorems/ff0fd54f-fc85-43fe-90aa-82698d864e71
-- title:
--   The curve ideal `(f + π ∑ zᵢ bᵢ)` lies in the residue cell of `f`.
-- statement:
--   The curve ideal `(f + π ∑ zᵢ bᵢ)` lies in the residue cell of `f`.
-- source:
--   TypeDensity/Measure/AdicCylinders.lean#L607-L617

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Theorems.Thm_TypeDensity_coordinateLift_smul_eq_mul
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

theorem TypeDensity.coordinate_ideal_in_residue_cell (O R : Type) [CommRing O] [CommRing R] [Algebra O R]
    (n : ℕ) (pi : O) (b : Fin n → R) (f : R) (z : Fin n → O) :
    coordinateIdeal pi f b z ∈ residueIdealCell (algebraMap O R pi) f := by sorry
