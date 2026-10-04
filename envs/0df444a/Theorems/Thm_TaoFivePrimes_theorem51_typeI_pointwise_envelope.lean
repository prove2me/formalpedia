-- Prove2me | Theorems.Thm_TaoFivePrimes_theorem51_typeI_pointwise_envelope
-- name    : TaoFivePrimes.theorem51_typeI_pointwise_envelope
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-14T17:47:21.074986+00:00
-- url     : https://prove2.me/theorems/9abeeaa8-a111-4678-9d85-02e20678109b
-- title:
--   Tao Section 5: the pointwise envelope for a Type I summand
-- statement:
--   **The pointwise envelope for a single Type I summand.** Let $U,V\ge40$ with $U,V<x$, $UV\le\frac x4$ and $UV^2\ge x$, let $(c_d)$ be complex coefficients with $|c_d|\le1$ on the positive odd $d\le UV$, and fix such a $d$. Then
--
--   $$\Bigl|\sum_{m\text{ odd}}\bigl(\log m+c_d\log d\bigr)\eta_0\!\Bigl(\frac{dm}{x}\Bigr)e(\alpha dm)\Bigr|\ \le\ \min\Bigl(\frac12\frac xd\log x+4(\log2)\log 2x,\ \frac{4(\log2)\log 2x}{|\sin(2\pi d\alpha)|}\Bigr),$$
--
--   with the convention that the second alternative is dropped when $\sin(2\pi d\alpha)=0$.
--
--   This is the source's display (amble): the whole analytic content of the Type I estimate, before any summation over $d$. It follows from the summation-by-parts corollary applied to $F(y)=\eta_0(dy/x)(\log y+c_d\log d)$, which gives the three-fold minimum of $\frac12\|F\|_{L^1}+\frac12\|F'\|_{L^1}$, $\frac{\|F'\|_{L^1}}{2|\sin(2\pi d\alpha)|}$ and $\frac{\|F''\|_{L^1}}{2|\sin(2\pi d\alpha)|^2}$, together with the norms
--   $$\|\eta_0\|_{L^1}=1,\quad\|\eta_0\|_{L^\infty}=4\log2,\quad\|\eta_0'\|_{L^1}=8\log2,\quad\|\eta_0'\|_{L^\infty}=16,\quad\|\eta_0''\|_{L^1}=48,$$
--   and the support of $\eta_0$ in $[\frac14,1]$, which gives $|\log y+c_d\log d|\le\log x$ on the support of $y\mapsto\eta_0(dy/x)$. Only the first two of the three alternatives are retained here; the third is what the source uses for its alternative estimate in the range $a=\pm1$, $UV<q-1$, which is not needed for Theorem 1.3.
--
--   **Formalization Note** The source's $\eta_0$ is only piecewise smooth, so the summation-by-parts corollary is applied after an infinitesimal mollification, or with the $L^1$ norms of the derivatives read as total variations; the statement above is the conclusion of that limiting argument and is what the rest of Section 5 uses. The sum is over all odd integers $m=2n+1$, $n\in\mathbb Z$, and is finite because $\eta_0$ has compact support. The sine is written $\sin(\pi\cdot2\alpha\cdot d)$.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 5, estimation of the Type I sum, the display (amble) bounding a single summand

import Mathlib
import Definitions.Def_TaoFivePrimes_Theorem51Sums

open Finset

theorem TaoFivePrimes.theorem51_typeI_pointwise_envelope
    (x alpha U V : ℝ) (hx : 0 < x) (hU40 : 40 ≤ U) (hV40 : 40 ≤ V)
    (hUx : U < x) (hVx : V < x) (hUV : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2)
    (c : ℕ → ℂ) (hc : ∀ d ∈ TaoFivePrimes.theorem51Divisors U V, ‖c d‖ ≤ 1)
    (d : ℕ) (hd : d ∈ TaoFivePrimes.theorem51Divisors U V) :
    ‖∑' n : ℤ,
        (((Real.log ((2 * n + 1 : ℤ) : ℝ) : ℂ) + c d * (Real.log d : ℂ)) *
          (TaoFivePrimes.eta0 (d * ((2 * n + 1 : ℤ) : ℝ) / x) : ℂ)) *
          TaoFivePrimes.expCircle (alpha * d * ((2 * n + 1 : ℤ) : ℝ))‖
      ≤ (if Real.sin (Real.pi * (2 * alpha) * (d : ℝ)) = 0 then
            (1 / 2) * (x / (d : ℝ)) * Real.log x + 4 * Real.log 2 * Real.log (2 * x)
          else min ((1 / 2) * (x / (d : ℝ)) * Real.log x + 4 * Real.log 2 * Real.log (2 * x))
            (4 * Real.log 2 * Real.log (2 * x)
              / |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))|)) := by sorry
