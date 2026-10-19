-- Prove2me | Theorems.Thm_TypeDensity_finite_coordinate_linear_continuous
-- name    : TypeDensity.finite_coordinate_linear_continuous
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:08.836406+00:00
-- url     : https://prove2.me/theorems/d3dee353-7866-4082-b632-f931fd291900
-- title:
--   Every `O`-linear map `O^m → O^n` is continuous.
-- statement:
--   Every `O`-linear map `O^m → O^n` is continuous.
-- source:
--   TypeDensity/Measure/AdicCylinders.lean#L983-L987

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

theorem TypeDensity.finite_coordinate_linear_continuous (O : Type) [CommRing O] [TopologicalSpace O]
    [IsTopologicalRing O] (m n : ℕ) (L : (Fin m → O) →ₗ[O] (Fin n → O)) :
    Continuous L := by sorry
