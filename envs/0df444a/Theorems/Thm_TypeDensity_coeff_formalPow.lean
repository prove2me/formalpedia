-- Prove2me | Theorems.Thm_TypeDensity_coeff_formalPow
-- name    : TypeDensity.coeff_formalPow
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:53.579563+00:00
-- url     : https://prove2.me/theorems/033ff766-ebf8-44ee-bf21-ee66e3ffee60
-- title:
--   Binomial expansion of the formal power: the `n`-th coefficient of `g^c` is `Σ_{k ≤ n} (1/k!) c(c-1)⋯(c-k+1) [xⁿ](g-1)^k`.
-- statement:
--   Binomial expansion of the formal power: the `n`-th coefficient of `g^c` is `Σ_{k ≤ n} (1/k!) c(c-1)⋯(c-k+1) [xⁿ](g-1)^k`.
-- source:
--   TypeDensity/Reciprocity/Plethysm.lean#L182-L216

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_binomial_series_ode
import Theorems.Thm_TypeDensity_constantCoeff_expSer
import Theorems.Thm_TypeDensity_derivative_expSer
import Theorems.Thm_TypeDensity_constantCoeff_logSer
import Theorems.Thm_TypeDensity_mul_derivative_logSer
import Theorems.Thm_TypeDensity_coeff_subst_eq_sum
import Theorems.Thm_TypeDensity_eq_of_mul_derivative_eq_mul
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

theorem TypeDensity.coeff_formalPow (c : RatFunc ℚ) (g : Ser) (hg : PowerSeries.constantCoeff g = 1)
    (n : ℕ) :
    PowerSeries.coeff n (formalPow c g) = ∑ k ∈ Finset.range (n + 1), ((k.factorial : ℚ)⁻¹) •
      ((∏ j ∈ Finset.range k, (scalar c - (j : ℚ) • (1 : Coef))) *
        PowerSeries.coeff n ((g - 1) ^ k)) := by sorry
