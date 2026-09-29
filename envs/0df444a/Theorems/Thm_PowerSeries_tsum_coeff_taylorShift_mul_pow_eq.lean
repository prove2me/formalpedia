-- Prove2me | Theorems.Thm_PowerSeries_tsum_coeff_taylorShift_mul_pow_eq
-- name    : PowerSeries.tsum_coeff_taylorShift_mul_pow_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/fa15cb0a-597d-5e15-b36f-c76185054bcc
-- title:
--   Taylor shift recentres a bounded power series
-- statement:
--   Let $L$ be a nontrivially normed field which is complete and whose distance is ultrametric, and let $F \in L[[T]]$ be a formal power series. Suppose $\rho > 0$ and $M \in \mathbb{R}$ are such that $\|\mathrm{coeff}_n F\| \cdot \rho^n \le M$ for every $n \in \mathbb{N}$, i.e. $F$ is bounded by $M$ at radius $\rho$. Let $a, b \in L$ with $\|a\| < \rho$ and $\|b\| < \rho$. Form the power series whose $n$-th coefficient is the (unconditional) sum $\sum_{k} \mathrm{coeff}_{n+k}(F) \cdot \binom{n+k}{n} \cdot a^{k}$, the binomial coefficient being taken as an element of $L$ via the natural cast. The assertion is the equality of the two sums $$\sum_{n} \Big(\sum_{k} \mathrm{coeff}_{n+k}(F)\binom{n+k}{n} a^{k}\Big) b^{n} = \sum_{n} \mathrm{coeff}_n(F)\,(a+b)^{n},$$ both sums being `tsum`s over $\mathbb{N}$ in $L$. In words: evaluating the Taylor shift of $F$ at $a$ at the point $b$ gives the value of $F$ at $a + b$.
--
--   This is the recentring identity of non-archimedean function theory: on a disc of radius $\rho$ on which the Gauss-type bound holds, the Taylor shift of $F$ at $a$ represents the same function expanded about $a$. It is used for the formal matching of chart expansions after recentring, being cited in the construction of charts at pivot points on a modular curve and in the multiplicativity of the Taylor shift.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PowerSeries_tsum_coeff_taylorShift_mul_pow_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PowerSeries.tsum_coeff_taylorShift_mul_pow_eq {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
    (F : PowerSeries L) {ρ M : ℝ} (hρ : 0 < ρ) (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M)
    (a : L) (ha : ‖a‖ < ρ) (b : L) (hb : ‖b‖ < ρ) :
    ∑' n, PowerSeries.coeff n (PowerSeries.mk fun n => ∑' k : ℕ,
        PowerSeries.coeff (n + k) F * ((n + k).choose n : L) * a ^ k) * b ^ n
      = ∑' n, PowerSeries.coeff n F * (a + b) ^ n := by sorry
