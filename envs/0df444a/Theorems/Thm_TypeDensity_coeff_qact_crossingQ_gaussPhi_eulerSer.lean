-- Prove2me | Theorems.Thm_TypeDensity_coeff_qact_crossingQ_gaussPhi_eulerSer
-- name    : TypeDensity.coeff_qact_crossingQ_gaussPhi_eulerSer
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:00:42.205907+00:00
-- url     : https://prove2.me/theorems/d4cf0577-792b-449d-918e-e25f1659b9fc
-- title:
--   The `n`-th coefficient of `ρ(U_{a,a}) Φ(G_a)`, expanded by divisor degree `d` and crossing depth `r` into crossing laws and pattern sums (plus `1` in degree `0`).
-- statement:
--   The `n`-th coefficient of `ρ(U_{a,a}) Φ(G_a)` is expanded by divisor degree `d` and crossing depth `r` into crossing laws and pattern sums (plus `1` in degree `0`).
-- source:
--   TypeDensity/Reciprocity/Patterns.lean#L942-L991

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Definitions.Def_TypeDensity_Reciprocity_Patterns
import Theorems.Thm_TypeDensity_qpow_zero
import Theorems.Thm_TypeDensity_coeff_qact_gaussPhi
import Theorems.Thm_TypeDensity_patternSum_eq_of_le
import Theorems.Thm_TypeDensity_rational_divisorProbability_single
import Theorems.Thm_TypeDensity_coeff_eulerSer
import Theorems.Thm_TypeDensity_coeff_zero_eulerSer
import Theorems.Thm_TypeDensity_scalar_mul
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

theorem TypeDensity.coeff_qact_crossingQ_gaussPhi_eulerSer (a n : ℕ) (ha : 0 < a) :
    PowerSeries.coeff n (qact (crossingQ a a) (gaussPhi (eulerSer 0 a))) =
        (∑ d ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (d + 1),
        (if ((0 < r ↔ d < n) ∧ r ≤ d) then scalar (divisorProbability (State.single a n)
        d).rational * ((if r = 0 then 1 else lawCoef (stateLaw (State.crossing a a r (n - d)))) *
        patternSum 0 a (a * n) (d - r)) else 0)) + (if n = 0 then 1 else 0) := by sorry
