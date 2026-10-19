-- Prove2me | Theorems.Thm_TypeDensity_coefficient_uniformizer_cylinder_mass
-- name    : TypeDensity.coefficient_uniformizer_cylinder_mass
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:13.105918+00:00
-- url     : https://prove2.me/theorems/9a51c521-fc88-44ea-9053-35be3a3e440c
-- title:
--   The coefficient measure of a `π`-adic cylinder of level `j` in `O^n` is `q^(-nj)`.
-- statement:
--   The coefficient measure of a `π`-adic cylinder of level `j` in `O^n` is `q^(-nj)`.
-- source:
--   TypeDensity/Measure/HenselProducts.lean#L1248-L1265

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Theorems.Thm_TypeDensity_finite_coordinate_adic_congruence
import Theorems.Thm_TypeDensity_coefficient_cylinder_mass
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
set_option autoImplicit false

open TypeDensity
open MeasureTheory
open scoped BigOperators ENNReal

theorem TypeDensity.coefficient_uniformizer_cylinder_mass (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ) (pi : O) (hp : Irreducible pi) (j : ℕ)
    (x : Fin n → O) :
    coefficientMeasure O n {z | adicCongr (Ideal.span {pi}) j z x} =
      (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹^(n*j) := by sorry
