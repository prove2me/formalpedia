-- Prove2me | Theorems.Thm_TypeDensity_sum_triple_reindex
-- name    : TypeDensity.sum_triple_reindex
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:50.930987+00:00
-- url     : https://prove2.me/theorems/8414359f-ea15-4510-8a7f-c08f8b3c2411
-- title:
--   Reindexing a triple sum over `(rx, m, rt)` with `rx + m + rt ≤ K` by the total `d = rx + m + rt`.
-- statement:
--   A triple sum over `(rx, m, rt)` with `rx + m + rt ≤ K` is reindexed by the total `d = rx + m + rt`.
-- source:
--   TypeDensity/Reciprocity/Plethysm.lean#L644-L678

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
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
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Log
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.sum_triple_reindex (c K : ℕ) (hK : K ≤ c) (G : ℕ → ℕ → ℕ → Coef) :
    ∑ rx ∈ Finset.range (c + 1), ∑ m ∈ Finset.range (c + 1), ∑ rt ∈ Finset.range (c + 1),
        (if rx + m + rt ≤ K then G rx m rt else 0) = ∑ d ∈ Finset.range (c + 1),
        ∑ rt ∈ Finset.range (d + 1), ∑ rx ∈ Finset.range (d + 1),
        (if (rt + rx ≤ d ∧ d ≤ K) then G rx (d - rt - rx) rt else 0) := by sorry
