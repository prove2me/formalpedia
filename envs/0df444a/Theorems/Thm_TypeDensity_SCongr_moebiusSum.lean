-- Prove2me | Theorems.Thm_TypeDensity_SCongr_moebiusSum
-- name    : TypeDensity.SCongr.moebiusSum
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:32:01.23106+00:00
-- url     : https://prove2.me/theorems/92227911-5f4b-4e07-849d-1d5c18228421
-- title:
--   Truncated agreement `f ≡ g mod x^{n+1}` is preserved by `moebiusSum = Σ μ(k) ψ_k/k`.
-- statement:
--   Truncated agreement `f ≡ g mod x^{n+1}` is preserved by `moebiusSum = Σ μ(k) ψ_k/k`.
-- source:
--   TypeDensity/Reciprocity/Plethysm.lean#L47-L51

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

theorem TypeDensity.SCongr.moebiusSum {n : ℕ} {f g : Ser} (h : SCongr n f g) :
    SCongr n (TypeDensity.moebiusSum f) (TypeDensity.moebiusSum g) := by sorry
