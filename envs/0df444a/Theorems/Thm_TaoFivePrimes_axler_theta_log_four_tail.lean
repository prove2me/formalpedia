-- Prove2me | Theorems.Thm_TaoFivePrimes_axler_theta_log_four_tail
-- name    : TaoFivePrimes.axler_theta_log_four_tail
-- status  : Open
-- author  : @lt9
-- created : 2026-09-28T14:01:14.436187+00:00
-- url     : https://prove2.me/theorems/3e9f393e-c00f-42f7-9208-f2e2f87d5814
-- title:
--   Axler theta error, analytic range: $|\vartheta(x)-x|<100x/\log^4x$ for $x\ge10^8$
-- statement:
--   **The analytic half of Axler's explicit fourth-power theta estimate.**
--
--   Let
--   $$\vartheta(x)=\sum_{p\le x}\log p$$
--   be the Chebyshev theta function. This node asserts the pointwise estimate
--
--   $$\bigl|\vartheta(x)-x\bigr|<\frac{100\,x}{\log^4 x}\qquad\text{for every real }x\ge10^8 .$$
--
--   It is the analytic half of Proposition 1 of Axler (2018), which is stated for all $x\ge70111$. Splitting that proposition at $x=10^8$ separates the two logically different ingredients: on $[70111,10^8)$ the estimate is a finite verification, while from $10^8$ on it follows from the explicit relation between $\vartheta$ and the zeros of the Riemann zeta function. This node is the analytic ingredient.
--
--   **Role.** This is a quantitative prime number theorem statement: since $\vartheta(x)\sim x$, it says the relative error of $\vartheta(x)$ is at most $100/\log^4x$, i.e. below $0.087\%$ from $x=10^8$ on. Above $10^8$ this estimate is far from tight ($\vartheta(x)-x$ is of size $\sqrt x$ up to logarithmic factors, whereas $100x/\log^4x$ is larger by a factor $\approx\frac14\sqrt x\log^3x$ at $x=10^8$), so the constant $100$ is comfortable in this range; the source needs the analytic estimate in this form because it is then fed into partial summation against the kernel $(\log t+1)/(t^2\log^2t)$. Together with the companion node `TaoFivePrimes.axler_theta_log_four_finite_certificate` it yields the target statement `TaoFivePrimes.axler_theta_error_log_four` on the whole range $x\ge70111$.
--
--   **Formalization Note.** The statement is unconditional and uniform in $x\ge10^8$; equivalently, writing $E(t)=\vartheta(t)-t$, it says $|E(t)|<100t/\log^4t$ for all $t\ge10^8$.
-- source:
--   Christian Axler, New Estimates for Some Functions Defined over Primes, Integers 18 (2018), A52, p. 6, Proposition 1, equation (2.4). https://math.colgate.edu/~integers/s52/s52.pdf -- restricted to the analytic range x >= 10^8.

import Mathlib
open Finset

theorem TaoFivePrimes.axler_theta_log_four_tail (x : ℝ) (h1 : 10 ^ 8 ≤ x) :
  |(∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log (p : ℝ)) - x| <
    100 * x / (Real.log x) ^ 4 := by sorry
