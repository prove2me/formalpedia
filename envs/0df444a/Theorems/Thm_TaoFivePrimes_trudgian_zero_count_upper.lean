-- Prove2me | Theorems.Thm_TaoFivePrimes_trudgian_zero_count_upper
-- name    : TaoFivePrimes.trudgian_zero_count_upper
-- status  : Open
-- author  : @Gabewhigham
-- created : 2026-09-30T14:24:35.744981+00:00
-- url     : https://prove2.me/theorems/cf3e90dd-c7ef-4759-861f-2b238a1aaf05
-- title:
--   Trudgian's explicit Riemann–von Mangoldt upper bound for $N(T)$
-- statement:
--   **Explicit Riemann–von Mangoldt formula (upper bound).** For $T>0$ let $N(T)$ denote the number of zeros $\rho=\beta+i\gamma$ of the Riemann zeta function with $0<\beta<1$ and $0<\gamma\le T$, **counted with multiplicity**. Then for every $T\ge e$,
--
--   $$N(T)\;\le\;\frac{T}{2\pi}\log\frac{T}{2\pi e}+\frac78+0.112\log T+0.278\log\log T+2.51+\frac{0.2}{T}.$$
--
--   This is the upper half of Trudgian's explicit form $\bigl|N(T)-\frac{T}{2\pi}\log\frac{T}{2\pi e}-\frac78\bigr|\le 0.112\log T+0.278\log\log T+2.510+0.2/T$ of the Riemann–von Mangoldt formula. Evaluated at $T_0=3.29\times10^9$ it gives $N(T_0)<10^{10}$, which is the zero count in Theorem 1.5 of Tao's paper; it is also the kind of bound needed for $N(T_0)$ in Tao's Proposition 7.2.
--
--   **Formalization Note** $N(T)$ is the finite sum of `analyticOrderNatAt riemannZeta s` over the zeros $s$ in the region; at each such zero $\zeta$ is analytic and not locally zero, so this is the multiplicity. Zeros with ordinate exactly $T$ are counted with full weight; since the right-hand side is continuous in $T$ and $N$ is right-continuous, this follows from the source bound whatever convention is used at ordinates.
-- source:
--   T. Trudgian, An improved upper bound for the argument of the Riemann zeta-function on the critical line II, Journal of Number Theory 134 (2014), 280-292, Corollary 1 (explicit bound for N(T), valid for T >= e); used for the zero count in Theorem 1.5 (p. 7) of T. Tao, https://arxiv.org/abs/1201.6656.

import Mathlib

namespace TaoFivePrimes

theorem trudgian_zero_count_upper (T : ℝ) (hT : Real.exp 1 ≤ T) :
    (∑ᶠ s ∈ {s : ℂ | 0 < s.re ∧ s.re < 1 ∧ 0 < s.im ∧ s.im ≤ T ∧ riemannZeta s = 0},
        (analyticOrderNatAt riemannZeta s : ℝ)) ≤
      T / (2 * Real.pi) * Real.log (T / (2 * Real.pi * Real.exp 1)) + 7 / 8
        + 0.112 * Real.log T + 0.278 * Real.log (Real.log T) + 2.51 + 0.2 / T := by
  sorry

end TaoFivePrimes
