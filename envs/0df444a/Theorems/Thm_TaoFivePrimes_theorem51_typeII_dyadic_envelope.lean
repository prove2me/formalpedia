-- Prove2me | Theorems.Thm_TaoFivePrimes_theorem51_typeII_dyadic_envelope
-- name    : TaoFivePrimes.theorem51_typeII_dyadic_envelope
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-14T17:38:14.530279+00:00
-- url     : https://prove2.me/theorems/84c50127-41c8-42e6-9e1f-16e17e78ab14
-- title:
--   Tao Section 5: the dyadic envelope for the Type II sum
-- statement:
--   **The dyadic envelope for Tao's Type II sum.** Let $q\ge4$ with $(a,q)=1$, let $4\alpha=\frac aq+\beta$ with $|\beta|\le q^{-2}$, and let $U,V\ge40$ with $U,V<x$, $UV\le\frac x4$ and $UV^2\ge x$. Then there is a nonnegative function $G$ on $\mathbb R$, supported in $[V,\frac xU]$, with $W\mapsto G(W)/W$ integrable on $(0,\infty)$, such that
--
--   $$G(W)\ \le\ \frac{1.1}{8}\Bigl(\frac1{2\sqrt2}\frac{x}{\sqrt q}+\frac12\sqrt{xW}+\frac{x}{\sqrt W}+\sqrt2\,\sqrt{xq}\Bigr)\log W\qquad (V\le W\le \tfrac xU)$$
--
--   and
--
--   $$T_{II}(x,\alpha,U,V)\ \le\ 4\int_0^\infty G(W)\,\frac{dW}{W},$$
--
--   where $T_{II}$ is the bilinear Type II sum of the platform interface.
--
--   This is the whole arithmetic content of the source's Type II estimate. The function $G$ is
--   $$G(W)=\Bigl|\sum_{\substack{d>U,\ w>V\\ d,w\text{ odd}}}\mu(d)\,g(w)\,\mathbf 1_{[x/2W,\,x/W]}(d)\,\mathbf 1_{[W/2,\,W]}(w)\,e(\alpha dw)\Bigr| ,$$
--   the dyadic block of the bilinear sum; the inequality $T_{II}\le4\int_0^\infty G\frac{dW}{W}$ comes from the dyadic integral representation of $\eta_0$ together with the triangle inequality, the support statement from the fact that the two blocks are both nonempty only for $V\le W\le\frac xU$, and the pointwise envelope from the subdivision form of the odd bilinear large sieve with $M=\frac q2$, using $\delta\ge\frac1{2q}$, $|g(w)|\le\frac12\log w$, and the counting bounds for the two blocks. All of these ingredients are public and proved on the platform: `TaoFivePrimes.eta0_dyadic_integral`, `TaoFivePrimes.large_sieve_subdivision`, `TaoFivePrimes.typeII_counting_bounds` and `TaoFivePrimes.typeII_sqrt_expansion`.
--
--   **Formalization Note** The envelope carries the coefficient $1$ on $\frac{x}{\sqrt W}$, matching `TaoFivePrimes.typeII_sqrt_expansion`; the source's printed $\frac1{\sqrt2}$ is a slip. Existential form is used so that this statement carries no commitment to a particular normalisation of the dyadic blocks.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 5, estimation of the Type II sum, the dyadic representation of eta0 and the large sieve bound for F(W)

import Mathlib
import Definitions.Def_TaoFivePrimes_Theorem51Sums

open MeasureTheory

theorem TaoFivePrimes.theorem51_typeII_dyadic_envelope
    (x alpha beta : ℝ) (a : ℤ) (q : ℕ) (hq : 4 ≤ q)
    (haq : Nat.Coprime a.natAbs q)
    (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (U V : ℝ) (hU40 : 40 ≤ U) (hV40 : 40 ≤ V) (hUx : U < x) (hVx : V < x)
    (hUV : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    ∃ G : ℝ → ℝ,
      (∀ W, 0 ≤ G W) ∧
      (∀ W, W ∉ Set.Icc V (x / U) → G W = 0) ∧
      MeasureTheory.IntegrableOn (fun W => G W / W) (Set.Ioi 0) ∧
      (∀ W ∈ Set.Icc V (x / U),
        G W ≤ (1.1 / 8) * ((1 / (2 * Real.sqrt 2)) * (x / Real.sqrt (q : ℝ))
              + (1 / 2) * Real.sqrt (x * W) + x / Real.sqrt W
              + Real.sqrt 2 * Real.sqrt (x * (q : ℝ))) * Real.log W) ∧
      TaoFivePrimes.theorem51TypeII x alpha U V ≤ 4 * ∫ W in Set.Ioi (0:ℝ), G W / W := by sorry
