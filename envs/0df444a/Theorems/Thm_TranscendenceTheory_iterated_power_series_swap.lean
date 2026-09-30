-- Prove2me | Theorems.Thm_TranscendenceTheory_iterated_power_series_swap
-- name    : TranscendenceTheory.iterated_power_series_swap
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-14T21:36:07.15817+00:00
-- url     : https://prove2.me/theorems/e9b937be-7ac6-4007-90ea-2a70d14528a5
-- title:
--   Variable swap for iterated formal power series
-- statement:
--   Let R be a semiring. There is a unique ring equivalence τ of the iterated formal power-series semiring R[[x]][[z]] with itself such that, for every series f and all nonnegative integers i,k,
--
--   $$[x^i][z^k]\,\tau(f)=[x^k][z^i]f.$$
--
--   Thus τ exchanges the two formal variables, preserving addition, multiplication and their identities. The coefficient ring R need not be commutative, and no convergence condition is imposed.
--
--   This equivalence allows an identity whose coefficients are local formal series to be read instead as a family of generating functions for individual local jets.
-- source:
--   Derived formal variable-swap step for https://prove2.me/theorems/502b648c-9242-45b3-9dd0-0ae62ba7a0ba. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1; https://doi.org/10.1017/S001309152610145X. This is an algebraic tool for the interpolation frontier; the geometric zero estimate remains open. Primary Lean sources: Mathlib RingTheory/PowerSeries/Basic.lean (coeff_mul, coeff_mk, ext, C and map) and Inverse.lean (mul_invOfUnit), revision 0df444a360eaa60ab8c11dca51a86af692955474; https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/PowerSeries/Basic.html. Transposing the coefficient array is a ring equivalence because each product coefficient is a finite double convolution. The frontier uses this equivalence to collect each local jet as a generating series in the power index, with a proved denominator-inverse certificate. All interpolation witnesses, weights, and numerical bounds are preserved.

import Mathlib.RingTheory.PowerSeries.Basic

open PowerSeries

theorem TranscendenceTheory.iterated_power_series_swap
    (R : Type*) [Semiring R] :
    ∃! τ : PowerSeries (PowerSeries R) ≃+* PowerSeries (PowerSeries R),
      ∀ (f : PowerSeries (PowerSeries R)) (i k : ℕ),
        PowerSeries.coeff i (PowerSeries.coeff k (τ f)) =
          PowerSeries.coeff k (PowerSeries.coeff i f) := by sorry
