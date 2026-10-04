-- Prove2me | Theorems.Thm_TaoFivePrimes_exp_sum_estimate_from_minor_arc_bound
-- name    : TaoFivePrimes.exp_sum_estimate_from_minor_arc_bound
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-14T15:44:55.317349+00:00
-- url     : https://prove2.me/theorems/9ec56cd5-5d5c-4eb7-9fe5-81917e99b352
-- title:
--   Tao Section 6: the exponential sum estimate from the minor arc bound
-- statement:
--   Let $x\ge10^{20}$, let $4\alpha=\frac aq+\beta$ with $100\le q\le x/100$, $(a,q)=1$ and $|\beta|\le q^{-2}$, and let every prime factor of the sifting modulus $q_0$ be at most $\sqrt x$. Assume the minor-arc bound for smoothed prime exponential sums: for every admissible pair $U,V$ — that is, $1<U,V<x$ with $UV\le\frac x4$, $UV^2\ge x$ and $U,V\ge40$ —
--
--   $$\begin{aligned}
--   |S_{\eta_0,2}(x,\alpha)|\ \le\ & 0.5\,\frac xq(\log x)\log\Bigl(\frac{2UV}{q}+4\Bigr)+0.89\Bigl(UV+\frac52q\Bigr)(8+\log q)\log(2x)\\
--   &+\Bigl(0.1\frac{x}{\sqrt q}+0.39\frac{x}{\sqrt{x/q}}\Bigr)\Bigl(\log\frac{x}{UV}\Bigr)\log\frac{Vx}{U}+\Bigl(0.55\frac{x}{\sqrt U}+0.78\frac{x}{\sqrt V}\Bigr)\log\frac xU .
--   \end{aligned}$$
--
--   Then
--
--   $$|S_{\eta_0,q_0}(x,\alpha)|\ \le\ \Bigl(0.14\frac{x}{\sqrt q}+0.64\frac{x}{\sqrt{x/q}}+0.15\,x^{4/5}\Bigr)(\log x)(\log x+11.3).$$
--
--   This is the derivation of the source's exponential sum estimate from its minor-arc theorem: the whole content is the choice
--   $$U=\tfrac14x^{2/5},\qquad V=\tfrac12x^{2/5},$$
--   for which the admissibility conditions hold once $x\ge10^{20}$, followed by the numerical collapse of the four resulting terms. The source's three intermediate estimates for that collapse are
--   $$\log(8x^{1/5})\log(2x)\le\tfrac15\log x(\log x+11.3),\quad (8+\log q)\log 2x\le1.1\log x(\log x+11.3),\quad \log(2x^{3/5})\le0.011\log x(\log x+11.3),$$
--   after which the terms $0.4\frac xq$ and $2.45\frac{x}{x/q}$ are absorbed into $0.04\frac{x}{\sqrt q}$ and $0.245\frac{x}{\sqrt{x/q}}$ using $100\le q\le x/100$. The final step replaces the modulus $2$ by the general sifting modulus $q_0$, at the cost of relaxing $0.149x^{4/5}$ to $0.15x^{4/5}$; the statement licensing that replacement is the source's Lemma 4.1, which is public and proved on the platform as `TaoFivePrimes.smoothedExpSum_modulus_change`.
--
--   **Formalization Note** The minor-arc bound is carried as a hypothesis quantified over all admissible $U,V$, so that this statement isolates exactly the content of the source's Section 6 and can be proved independently of Section 5. The power $x^{4/5}$ is the real power `x ^ (4/5 : ℝ)`.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 6 (Proof of Theorem 1.3), the derivation of estimate (Sax) from Theorem 5.1 with U = x^{2/5}/4 and V = x^{2/5}/2

import Mathlib
import Definitions.Def_TaoFivePrimes_SmoothedExpSum
import Definitions.Def_TaoFivePrimes_RepresentationCount

open Finset

theorem TaoFivePrimes.exp_sum_estimate_from_minor_arc_bound
    (x α β : ℝ) (a : ℤ) (q q₀ : ℕ)
    (hx : (10 : ℝ) ^ 20 ≤ x)
    (hq : 100 ≤ q) (hqx : (q : ℝ) ≤ x / 100)
    (haq : Nat.Coprime a.natAbs q)
    (hα : 4 * α = (a : ℝ) / q + β)
    (hβ : |β| ≤ 1 / (q : ℝ) ^ 2)
    (hq₀ : ∀ p ∈ q₀.primeFactors, (p : ℝ) ≤ Real.sqrt x)
    (hminor : ∀ U V : ℝ, 1 < U → 1 < V → U < x → V < x → U * V ≤ x / 4 → x ≤ U * V ^ 2 →
        40 ≤ U → 40 ≤ V →
        ‖TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 2 x α‖ ≤
          0.5 * (x / q) * Real.log x * Real.log (2 * U * V / q + 4)
            + 0.89 * (U * V + (5 / 2) * q) * (8 + Real.log q) * Real.log (2 * x)
          + (0.1 * x / Real.sqrt q + 0.39 * x / Real.sqrt (x / q))
              * Real.log (x / (U * V)) * Real.log (V * x / U)
          + (0.55 * x / Real.sqrt U + 0.78 * x / Real.sqrt V) * Real.log (x / U)) :
    ‖TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 q₀ x α‖ ≤
      (0.14 * x / Real.sqrt q + 0.64 * x / Real.sqrt (x / q) + 0.15 * x ^ (4 / 5 : ℝ))
        * Real.log x * (Real.log x + 11.3) := by sorry
