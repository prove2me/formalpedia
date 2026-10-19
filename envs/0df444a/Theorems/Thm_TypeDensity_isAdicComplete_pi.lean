-- Prove2me | Theorems.Thm_TypeDensity_isAdicComplete_pi
-- name    : TypeDensity.isAdicComplete_pi
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:50.163731+00:00
-- url     : https://prove2.me/theorems/0cd4f4e1-9f86-403a-94e6-5d907f4cd3c7
-- title:
--   A finite product of `I`-adically complete modules is `I`-adically complete.
-- statement:
--   A finite product of `I`-adically complete modules is `I`-adically complete.
-- source:
--   TypeDensity/Measure/HenselProducts.lean#L600-L642

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

theorem TypeDensity.isAdicComplete_pi (O : Type) [CommRing O] (I : Ideal O) (ι : Type) [Finite ι]
    (M : ι → Type) [∀ j, AddCommGroup (M j)] [∀ j, Module O (M j)] [∀ j, IsAdicComplete I (M j)] :
    IsAdicComplete I (∀ j, M j) := by sorry
