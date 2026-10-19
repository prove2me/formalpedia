-- Prove2me | Theorems.Thm_TypeDensity_coordinate_constraint_count
-- name    : TypeDensity.coordinate_constraint_count
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:42.909975+00:00
-- url     : https://prove2.me/theorems/b4cfc734-ceec-4bf3-bdcb-adc2786f7e20
-- title:
--   Over a finite field `k`, the number of `f : ι → k` vanishing on `A` and nonvanishing on a disjoint `B` is `(|k| - 1)^|B| · |k|^(|ι| - |A| - |B|)`.
-- statement:
--   Over a finite field `k`, the number of `f : ι → k` vanishing on `A` and nonvanishing on a disjoint `B` is `(|k| - 1)^|B| · |k|^(|ι| - |A| - |B|)`.
-- source:
--   TypeDensity/Measure/AdicCylinders.lean#L567-L605

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

theorem TypeDensity.coordinate_constraint_count (k ι : Type) [Field k] [Fintype k] [Fintype ι]
    (A B : Finset ι) (hAB : Disjoint A B) :
    Nat.card {f : ι→k // (∀ i∈A, f i=0) ∧ (∀ i∈B, f i≠0)}
      = (Fintype.card k-1)^B.card * (Fintype.card k)^(Fintype.card ι-A.card-B.card) := by sorry
