-- Prove2me | Theorems.Thm_TypeDensity_powerSeries_quotient_length_eq_order
-- name    : TypeDensity.powerSeries_quotient_length_eq_order
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:55.603952+00:00
-- url     : https://prove2.me/theorems/20b155e8-2f59-4480-94f9-84303bf5e728
-- title:
--   `k[[X]]/(g)` has length equal to the order of `g`, and multiplication by `g` is injective iff `g ≠ 0`.
-- statement:
--   `k[[X]]/(g)` has length equal to the order of `g`, and multiplication by `g` is injective iff `g ≠ 0`.
-- source:
--   TypeDensity/Surfaces/PowerSeries.lean#L417-L443

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
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

theorem TypeDensity.powerSeries_quotient_length_eq_order (k : Type) [Field k] (g : PowerSeries k) :
    Module.length (PowerSeries k) (PowerSeries k ⧸ Ideal.span {g}) = g.order ∧
    (Function.Injective (fun w : PowerSeries k ↦ g * w) ↔ g ≠ 0) := by sorry
