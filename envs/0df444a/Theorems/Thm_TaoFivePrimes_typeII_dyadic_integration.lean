-- Prove2me | Theorems.Thm_TaoFivePrimes_typeII_dyadic_integration
-- name    : TaoFivePrimes.typeII_dyadic_integration
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-14T17:38:11.123797+00:00
-- url     : https://prove2.me/theorems/1972d5ef-abb5-41ac-868d-feec7c904fa5
-- title:
--   Tao Section 5: integrating the Type II dyadic envelope
-- statement:
--   **The dyadic integration step of Tao's Type II estimate.** Let $x>0$, $q\ge4$, $U,V\ge40$ with $UV\le\frac x4$, and let $G:\mathbb R\to\mathbb R$ be nonnegative, supported in $[V,\frac xU]$, with $W\mapsto G(W)/W$ integrable on $(0,\infty)$ and
--
--   $$G(W)\ \le\ \frac{1.1}{8}\Bigl(\frac1{2\sqrt2}\frac{x}{\sqrt q}+\frac12\sqrt{xW}+\frac{x}{\sqrt W}+\sqrt2\,\sqrt{xq}\Bigr)\log W\qquad (V\le W\le \tfrac xU).$$
--
--   Then
--
--   $$4\int_0^\infty G(W)\,\frac{dW}{W}\ \le\ \Bigl(0.1\frac{x}{\sqrt q}+0.39\frac{x}{\sqrt{x/q}}\Bigr)\Bigl(\log\frac{x}{UV}\Bigr)\log\frac{Vx}{U}+\Bigl(0.55\frac{x}{\sqrt U}+1.1\frac{x}{\sqrt V}\Bigr)\log\frac xU .$$
--
--   This is the final step of the source's Type II estimate, isolated from the arithmetic that produces $G$: once the dyadic envelope for the bilinear sum is in hand, what remains is a calculus computation. The two $W$-independent terms integrate against $\frac{4\,dW}{W}$ to $2\log\frac{x}{UV}\log\frac{Vx}{U}$, and the two $W$-dependent ones are handled by bounding $\log W$ by $\log\frac xU$ and integrating $W^{-1/2}$ and $W^{-3/2}$.
--
--   **Formalization Note** The envelope is stated with the coefficient $1$ on $\frac{x}{\sqrt W}$, which is what the square-root expansion gives: $\sqrt{2q}\cdot\sqrt{\frac{x}{2Wq}}\cdot\sqrt x=x\sqrt{\frac{2q}{2Wq}}=\frac{x}{\sqrt W}$. This is why the last constant of the conclusion is $1.1$ and not the source's printed $0.78$. The hypothesis on $G$ is imposed only on $[V,\frac xU]$, since $G$ vanishes elsewhere; the integral is the Bochner integral over $(0,\infty)$ against Lebesgue measure.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 5, estimation of the Type II sum, the integration of F(W) against 4 dW/W

import Mathlib

open MeasureTheory intervalIntegral

theorem TaoFivePrimes.typeII_dyadic_integration (x q U V : ℝ) (G : ℝ → ℝ)
    (hx : 0 < x) (hq : 4 ≤ q) (hU40 : 40 ≤ U) (hV40 : 40 ≤ V)
    (hUV : U * V ≤ x / 4)
    (hG0 : ∀ W, 0 ≤ G W)
    (hGsupp : ∀ W, W ∉ Set.Icc V (x / U) → G W = 0)
    (hGint : MeasureTheory.IntegrableOn (fun W => G W / W) (Set.Ioi 0))
    (hGb : ∀ W ∈ Set.Icc V (x / U),
        G W ≤ (1.1 / 8) * ((1 / (2 * Real.sqrt 2)) * (x / Real.sqrt q)
              + (1 / 2) * Real.sqrt (x * W) + x / Real.sqrt W
              + Real.sqrt 2 * Real.sqrt (x * q)) * Real.log W) :
    4 * ∫ W in Set.Ioi (0:ℝ), G W / W ≤
      (0.1 * x / Real.sqrt q + 0.39 * x / Real.sqrt (x / q))
          * Real.log (x / (U * V)) * Real.log (V * x / U)
        + (0.55 * x / Real.sqrt U + 1.1 * x / Real.sqrt V) * Real.log (x / U) := by sorry
