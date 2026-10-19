-- Prove2me | Theorems.Thm_TypeDensity_sum_C_mul_X_pow_pow
-- name    : TypeDensity.sum_C_mul_X_pow_pow
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:45.613356+00:00
-- url     : https://prove2.me/theorems/78fb953b-5eef-4dfa-bf7f-b4342aae5685
-- title:
--   Multinomial expansion of `(Σ_{r<n} b_{r+1} x^{m(r+1)})^k`.
-- statement:
--   The multinomial expansion of `(Σ_{r<n} b_{r+1} x^{m(r+1)})^k` holds: it is the sum over `κ` with `Σ κ = k` of multinomial coefficients times `∏ b_{r+1}^{κ_r}` times `x^{m Σ (r+1) κ_r}`.
-- source:
--   TypeDensity/Reciprocity/Defs.lean#L651-L666

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
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

theorem TypeDensity.sum_C_mul_X_pow_pow (m n k : ℕ) (b : ℕ → Coef) :
    (∑ r : Fin n, PowerSeries.C (b (r.val + 1)) * (PowerSeries.X : Ser) ^ (m * (r.val + 1))) ^ k =
    ∑ κ ∈ Finset.piAntidiag (Finset.univ : Finset (Fin n)) k,
      PowerSeries.C ((Nat.multinomial Finset.univ κ : Coef) * ∏ r : Fin n, b (r.val + 1) ^ κ r) *
        (PowerSeries.X : Ser) ^ (m * ∑ r : Fin n, (r.val + 1) * κ r) := by sorry
