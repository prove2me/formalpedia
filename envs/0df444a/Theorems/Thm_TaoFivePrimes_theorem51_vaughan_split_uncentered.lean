-- Prove2me | Theorems.Thm_TaoFivePrimes_theorem51_vaughan_split_uncentered
-- name    : TaoFivePrimes.theorem51_vaughan_split_uncentered
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-14T02:40:17.616427+00:00
-- url     : https://prove2.me/theorems/c7b7b877-ec99-4804-b9cb-bea6c2a12d56
-- title:
--   Tao Lemma 4.11 for $S_{\eta_0,2}$: the Vaughan Type I / Type II split, uncentred
-- statement:
--   Let $x,\alpha\in\mathbb R$ and let $U,V\ge40$ satisfy $U,V<x$, $UV\le x/4$ and $x\le UV^2$. Then there are complex coefficients $c_d$ with $|c_d|\le1$ for every odd $d\le UV$ such that
--
--   $$\bigl|S_{\eta_0,2}(x,\alpha)\bigr|\ \le\ T_I+T_{II}^{\flat},$$
--
--   where $S_{\eta_0,2}(x,\alpha)=\sum_n\Lambda(n)\mathbf 1_{(n,2)=1}\eta_0(n/x)e(\alpha n)$ is the smoothed prime exponential sum sifted at the modulus $2$,
--
--   $$T_I=\sum_{\substack{d\le UV\\ d\ \mathrm{odd}}}\ \Bigl|\sum_{n\ \mathrm{odd}}\bigl(\log n+c_d\log d\bigr)\eta_0(dn/x)\,e(\alpha dn)\Bigr|$$
--
--   is the Type I envelope, and
--
--   $$T_{II}^{\flat}=\Bigl|\sum_{\substack{d>U\\ d\ \mathrm{odd}}}\ \sum_{\substack{w>V\\ w\ \mathrm{odd}}}\mu(d)\,g^{\flat}(w)\,\eta_0(dw/x)\,e(\alpha dw)\Bigr|,\qquad g^{\flat}(w)=\sum_{\substack{b\mid w\\ b>V}}\Lambda(b),$$
--
--   is the Type II sum with the **uncentred** divisor coefficient. Here $e(t)=e^{2\pi it}$, $\eta_0$ is the source's logarithmic cutoff supported in $[1/4,1]$, $\Lambda$ is von Mangoldt's function and $\mu$ is Möbius'.
--
--   This is the Vaughan decomposition that opens the source's minor-arc analysis: it replaces a sum over the primes by a linear (Type I) sum, in which the divisor variable is small and the exponential can be summed by parts, and a bilinear (Type II) sum, to which the large sieve applies. The Type I envelope is the one used verbatim in the source's Section 5.
--
--   **Deviation from the source** The source's Lemma 4.11 states the same split with the *centred* coefficient $g(w)=g^{\flat}(w)-\tfrac12\log w$, which improves the Type II sum by a factor of two. That improvement is charged to the Type I envelope: the leftover $\sum_{d>U}\sum_{w>V}\mu(d)\tfrac12(\log w)\,F(dw)$ has to be dominated by $\sum_{d\le UV}\bigl|\sum_n(\log n)F(dn)\bigr|$. The inner sums differ — the leftover is restricted to $w>V$ while the envelope is not — and on the range $x/(4V)\le d\le UV$, which is nonempty under these hypotheses, the unrestricted sum genuinely contains terms with $n\le V$ that can cancel the rest. The statement here therefore keeps the uncentred coefficient, for which the split is a direct consequence of Vaughan's identity, at the cost of $|g^{\flat}(w)|\le\log w$ in place of $|g(w)|\le\tfrac12\log w$.
--
--   **Formalization Note** The odd integers in the Type I inner sum are parametrized as $2n+1$ with $n$ ranging over $\mathbb Z$; the terms with $n<0$ vanish because $\eta_0$ is supported in the positive reals. Both the Type II sum and the smoothed sum are unconditional sums over the natural numbers, made finite by the compact support of $\eta_0$. The coefficient $g^{\flat}$ is written as `theorem51Centered V w + Real.log w / 2`, that is, as the platform's centred coefficient with the centring added back.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 4, Lemma 4.11 (A variant of Vaughan's identity), applied to the sum S_{eta0,2}(x,alpha) at the start of Section 5; the centring of the Type II coefficient by -log(w)/2 is dropped, see the Deviation note

import Mathlib
import Definitions.Def_TaoFivePrimes_Theorem51Sums

open Finset

theorem TaoFivePrimes.theorem51_vaughan_split_uncentered
    (x alpha U V : ℝ) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUx : U < x) (hVx : V < x)
    (hUVx : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    ∃ c : ℕ → ℂ,
      (∀ d ∈ TaoFivePrimes.theorem51Divisors U V, ‖c d‖ ≤ 1) ∧
      ‖TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 2 x alpha‖ ≤
        TaoFivePrimes.theorem51TypeI x alpha U V c +
          ‖∑' d : ℕ, ∑' w : ℕ,
            (if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2 then
              ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
                (((TaoFivePrimes.theorem51Centered V w + Real.log w / 2 : ℝ)) : ℂ) *
                TaoFivePrimes.expCircle (alpha * d * w) *
                ((TaoFivePrimes.eta0 ((d : ℝ) * (w : ℝ) / x) : ℝ) : ℂ)
            else 0)‖ := by sorry
