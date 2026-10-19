-- Prove2me | Theorems.Thm_TypeDensity_coeff_divisorTransform_comp
-- name    : TypeDensity.coeff_divisorTransform_comp
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:32:19.613503+00:00
-- url     : https://prove2.me/theorems/81903def-1aa8-4e67-b278-a0eef69b4763
-- title:
--   coeff divisorTransform comp
-- statement:
--   Composing two divisor transforms (`[xⁿ] ↦ Σ_{k ∣ n} w(k) ψ_k([x^{n/k}] f)`) with weights `a` and `b` gives the divisor transform with the Dirichlet convolution `a * b` as weight: the `n`-th coefficient is `Σ_{m ∣ n} (Σ_{k ∣ m} a(k) b(m/k)) ψ_m([x^{n/m}] f)`.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L288-L305

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_adamsCoef_adamsCoef
import Theorems.Thm_TypeDensity_sum_divisors_sum_divisors_div
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Log
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.coeff_divisorTransform_comp (a b : ℕ → ℚ) (f : Ser) (n : ℕ) :
    PowerSeries.coeff n (divisorTransform a (divisorTransform b f)) =
      ∑ m ∈ n.divisors, (∑ k ∈ m.divisors, a k * b (m / k)) •
        adamsCoef m (PowerSeries.coeff (n / m) f) := by sorry
