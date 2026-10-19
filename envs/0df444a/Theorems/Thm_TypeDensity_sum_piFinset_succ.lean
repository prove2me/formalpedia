-- Prove2me | Theorems.Thm_TypeDensity_sum_piFinset_succ
-- name    : TypeDensity.sum_piFinset_succ
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:00.420644+00:00
-- url     : https://prove2.me/theorems/a5338a14-b184-4e43-bd25-5bfa152a79d9
-- title:
--   Splitting a sum over `piFinset t` on `Fin (n + 1)` into the first coordinate and the tail.
-- statement:
--   A sum over `piFinset t` on `Fin (n + 1)` splits into the first coordinate and the tail.
-- source:
--   TypeDensity/Formula/LawAlgebra.lean#L549-L563

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
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
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.sum_piFinset_succ (n : ℕ) (t : Fin (n + 1) → Finset FactorType)
    (F : (Fin (n + 1) → FactorType) → ℚ) :
    ∑ τ ∈ Fintype.piFinset t, F τ
      = ∑ τ₀ ∈ t 0, ∑ τ' ∈ Fintype.piFinset (fun i ↦ t i.succ), F (Fin.cons τ₀ τ') := by sorry
