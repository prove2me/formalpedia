-- Prove2me | Theorems.Thm_TypeDensity_linear_map_preserves_adic_congruence
-- name    : TypeDensity.linear_map_preserves_adic_congruence
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:41.306405+00:00
-- url     : https://prove2.me/theorems/b378aeff-3427-4c7c-a007-9dc3c76880f4
-- title:
--   Linear maps preserve adic congruences.
-- statement:
--   Linear maps preserve adic congruences.
-- source:
--   TypeDensity/Measure/HenselProducts.lean#L644-L651

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
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

theorem TypeDensity.linear_map_preserves_adic_congruence (O M N : Type) [CommRing O] [AddCommGroup M]
    [Module O M] [AddCommGroup N] [Module O N] (I : Ideal O) (L : M →ₗ[O] N) (j : ℕ) (x y : M)
    (h : adicCongr I j x y) :
    adicCongr I j (L x) (L y) := by sorry
