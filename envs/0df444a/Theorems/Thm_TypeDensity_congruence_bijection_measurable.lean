-- Prove2me | Theorems.Thm_TypeDensity_congruence_bijection_measurable
-- name    : TypeDensity.congruence_bijection_measurable
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:41.67518+00:00
-- url     : https://prove2.me/theorems/7b351968-33c4-44c2-8910-70e3b553367b
-- title:
--   A surjection preserving and reflecting all adic congruences is measurable for the adic cylinder σ-algebra.
-- statement:
--   A surjection preserving and reflecting all adic congruences is measurable for the adic cylinder σ-algebra.
-- source:
--   TypeDensity/Measure/AdicCylinders.lean#L550-L565

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

theorem TypeDensity.congruence_bijection_measurable (O V : Type) [CommRing O] [AddCommGroup V] [Module O V]
    (I : Ideal O) [MeasurableSpace V] (hgen : ‹MeasurableSpace V› = adicCylinderSpace I V)
    (F : V → V) (honto : Function.Surjective F)
    (hcong : ∀ j x y, adicCongr I j (F x) (F y) ↔ adicCongr I j x y) :
    Measurable F := by sorry
