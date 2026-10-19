-- Prove2me | Theorems.Thm_TypeDensity_sum_patterns_scalar_mul_eq_patternSum
-- name    : TypeDensity.sum_patterns_scalar_mul_eq_patternSum
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:02:17.737066+00:00
-- url     : https://prove2.me/theorems/6c2bf01e-354e-4ce4-82b8-d49671744b79
-- title:
--   Summing the pattern terms `scalar (divisorCount ε m · Y) · B · Π ψ_{i+1}(F_{S(a;j+1)})^{m(i,j)}` over the patterns `m` of weight `w` gives `scalar Y · B · patternSum ε a N w`.
-- statement:
--   Summing the pattern terms `scalar (divisorCount ε m · Y) · B · Π ψ_{i+1}(F_{S(a;j+1)})^{m(i,j)}` over the patterns `m` of weight `w` gives `scalar Y · B · patternSum ε a N w`.
-- source:
--   TypeDensity/Reciprocity/Patterns.lean#L302-L313

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Definitions.Def_TypeDensity_Reciprocity_Patterns
import Theorems.Thm_TypeDensity_scalar_mul
import Theorems.Thm_TypeDensity_scalar_eq_algebraMap
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

theorem TypeDensity.sum_patterns_scalar_mul_eq_patternSum (ε : ℤ) (a N w : ℕ) (Y : RatFunc ℚ) (B : Coef) :
    ∑ m ∈ (Finset.univ : Finset (Pattern N)).filter (fun m ↦ patternWeight m = w),
      scalar ((divisorCount ε m).rational * Y) * (B * ∏ ij : Fin N × Fin N,
        (adamsCoef (ij.1.val + 1) (lawCoef (stateLaw (State.single a (ij.2.val + 1))))) ^
          (m ij).val) = scalar Y * (B * patternSum ε a N w) := by sorry
