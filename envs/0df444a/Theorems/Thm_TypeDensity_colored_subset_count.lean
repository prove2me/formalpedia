-- Prove2me | Theorems.Thm_TypeDensity_colored_subset_count
-- name    : TypeDensity.colored_subset_count
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:16.36916+00:00
-- url     : https://prove2.me/theorems/697af21b-8635-4c82-a568-f6a98baed35b
-- title:
--   The number of maps `Fin Q → Option (Fin r)` with exactly `m i` points of colour `i` is `Q (Q-1) ⋯ (Q - ∑ m + 1) / ∏ (m i)!`.
-- statement:
--   The number of maps `Fin Q → Option (Fin r)` with exactly `m i` points of colour `i` is `Q (Q-1) ⋯ (Q - ∑ m + 1) / ∏ (m i)!`.
-- source:
--   TypeDensity/Measure/AdicCylinders.lean#L521-L529

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

theorem TypeDensity.colored_subset_count (Q r : ℕ) (m : Fin r → ℕ) :
    ((Nat.card {f : Fin Q→Option (Fin r) //
      ∀ i : Fin r, Nat.card {x : Fin Q // f x=some i}=m i} : ℕ) : ℚ) =
      ((List.range (∑ i : Fin r, m i)).map fun j => (Q:ℚ)-j).prod
        / ∏ i : Fin r, (Nat.factorial (m i):ℚ) := by sorry
