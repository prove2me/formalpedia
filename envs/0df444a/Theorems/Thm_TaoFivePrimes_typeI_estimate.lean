-- Prove2me | Theorems.Thm_TaoFivePrimes_typeI_estimate
-- name    : TaoFivePrimes.typeI_estimate
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-14T04:44:48.945+00:00
-- url     : https://prove2.me/theorems/500ba892-4354-42f8-ab1a-92d3454a46a4
-- title:
--   Tao Theorem 5.1: the Type I estimate (with corrected constants)
-- statement:
--   Let $q\ge2$, let $a$ be coprime to $q$, and let $4\alpha=\frac aq+\beta$ with $|\beta|\le q^{-2}$. Let $x>0$, let $L,C\ge0$, and let $M\ge q/2$. Suppose a nonnegative weight $W$ obeys, for every $1\le d\le M$, the pointwise bound
--
--   $$W(d)\ \le\ \min\!\left(\tfrac12\frac xd L+C,\ \frac{C}{|\sin(2\pi d\alpha)|}\right)$$
--
--   (with the value $\tfrac12\frac xdL+C$ where the sine vanishes). Then
--
--   $$\sum_{\substack{1\le d\le M\\ d\ \mathrm{odd}}}W(d)\ \le\ \underbrace{2qC+\frac1\pi Cq\log 4q}_{d\le q/2}\ +\ \underbrace{\frac xqL\left(\log\Bigl(\frac{2M}{q}+4\Bigr)+4\right)+\Bigl(\Bigl\lfloor\frac{M}{2q}-\frac14\Bigr\rfloor+1\Bigr)\left(4C+\frac4\pi Cq\log 4q\right)}_{\text{blocks of length }2q}.$$
--
--   This is the Type I estimate of the source's minor-arc theorem. In the application $M=UV$ is the length of the divisor range, $L=\log x$, $C=4\log2\log 2x$, and $W(d)$ is the modulus of the inner exponential sum $\bigl|\sum_n(\log n+c_d\log d)\eta_0(dn/x)e(\alpha dn)\bigr|$, whose pointwise bound is what Corollary 3.2 supplies. The two pieces are the small divisors $d\le q/2$, where the frequency $4d\alpha$ is bounded away from the integers so the reciprocal-sine weight never exceeds $2q$, and the remaining range, cut into blocks of length $2q$ on each of which the weight $x/d$ is frozen at the left endpoint and the odd-restricted Vinogradov-type lemma is applied once.
--
--   **Deviation from the source** The source's corresponding display is
--   $$T_I\le 0.5\frac xq\log\Bigl(\frac{2UV}{q}+4\Bigr)\log x+0.89\Bigl(UV+\frac52q\Bigr)(8+\log q)\log 2x,$$
--   which its own chain does not give, for two independent reasons. First, the integral test it invokes drops an additive constant: the $j=0$ term of $\sum_j\frac{x}{2jq+q/2}$ alone equals $\frac{x}{2q}\cdot4$, so the claimed bound $\frac{x}{2q}\log(\frac{2UV}q+4)$ fails whenever $UV/q<\frac{e^4-4}2\approx25.3$ (at $q=1$, $UV=10$ the two sides are $2.8937x$ and $1.5890x$). Second, its per-block application of Corollary 3.5 uses the factor $1$ where the corollary gives $\lfloor\frac{2q}{2q}\rfloor+1=2$, the blocks having length exactly $2q$. The bound above is what the chain actually yields: the logarithm gains the additive $4$, the leading coefficient is $1$ rather than $\tfrac12$, and the block constant doubles. Nothing here contradicts the source's Theorem 5.1, whose statement carries further terms; only the intermediate Type I display is affected.
--
--   **Formalization Note** The divisor range is the odd integers of $(0,\lfloor M\rfloor]$. The truncation parameters are kept abstract as $L$ and $C$ rather than specialized to $\log x$ and $4\log2\log2x$. At the zeros of the sine the weight takes the value of the first argument of the minimum, which is the source's convention. The Vinogradov-type lemma of the source (its Lemma 3.4) is carried as the hypothesis `hvino`, quantified over the truncation level because the blocks use different ones; the odd-restricted Corollary 3.5 is imported and applied to it.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 5 (Minor arcs), subsection "Estimation of the Type I sum", the chain from equation (amble) to equation (ti-p); the constants are corrected, see the Deviation note

import Mathlib

open Finset

theorem TaoFivePrimes.typeI_estimate
    (alpha beta : ℝ) (a : ℤ) (q : ℕ) (hq : 2 ≤ q) (haq : Nat.Coprime a.natAbs q)
    (halpha : 4 * alpha = (a : ℝ) / q + beta) (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (x M Lx Cb : ℝ) (hx : 0 < x) (hLx : 0 ≤ Lx) (hCb : 0 ≤ Cb) (hM : (q : ℝ) / 2 ≤ M)
    (hvino : ∀ (A' alpha' beta' theta' u v : ℝ) (a' : ℤ),
        alpha' = (a' : ℝ) / q + beta' → |beta'| ≤ 1 / (q : ℝ) ^ 2 → u < v →
        (∑ n ∈ Finset.Ioc ⌊u⌋ ⌊v⌋,
            (if Real.sin (Real.pi * alpha' * (n : ℝ) + theta') = 0 then A'
              else min A' (Cb / |Real.sin (Real.pi * alpha' * (n : ℝ) + theta')|)))
          ≤ ((⌊(v - u) / (q : ℝ)⌋ : ℤ) + 1)
              * (2 * A' + (2 / Real.pi) * Cb * (q : ℝ) * Real.log (4 * q)))
    (W : ℤ → ℝ) (hW0 : ∀ d, 0 ≤ W d)
    (hWb : ∀ d : ℤ, 1 ≤ d → (d : ℝ) ≤ M →
        W d ≤ (if Real.sin (Real.pi * (2 * alpha) * (d : ℝ)) = 0 then
                  (1 / 2) * (x / (d : ℝ)) * Lx + Cb
                else min ((1 / 2) * (x / (d : ℝ)) * Lx + Cb)
                  (Cb / |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))|))) :
    (∑ d ∈ (Finset.Ioc (0 : ℤ) ⌊M⌋).filter (fun d : ℤ => Odd d), W d)
      ≤ (2 * (q : ℝ) * Cb + (1 / Real.pi) * Cb * (q : ℝ) * Real.log (4 * q))
        + ((x / q) * Lx * (Real.log (2 * M / q + 4) + 4)
           + ((⌊M / (2 * (q : ℝ)) - 1 / 4⌋₊ : ℝ) + 1)
               * (4 * Cb + (4 / Real.pi) * Cb * (q : ℝ) * Real.log (4 * q))) := by sorry
