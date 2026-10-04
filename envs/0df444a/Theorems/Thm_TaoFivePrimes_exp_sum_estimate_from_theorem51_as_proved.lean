-- Prove2me | Theorems.Thm_TaoFivePrimes_exp_sum_estimate_from_theorem51_as_proved
-- name    : TaoFivePrimes.exp_sum_estimate_from_theorem51_as_proved
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-14T18:04:01.397907+00:00
-- url     : https://prove2.me/theorems/3b61eb64-bad5-4653-8ad9-3bb7e2349055
-- title:
--   Tao Section 6 from Theorem 5.1 as its proof gives it
-- statement:
--   Let $x\ge10^{20}$, let $4\alpha=\frac aq+\beta$ with $100\le q\le x/100$, $(a,q)=1$ and $|\beta|\le q^{-2}$, and let every prime factor of $q_0$ be at most $\sqrt x$. Assume the minor-arc bound in the form the source's own argument yields: for every admissible $U,V$ — that is $1<U,V<x$ with $UV\le\frac x4$, $UV^2\ge x$, $U,V\ge40$ —
--   $$\begin{aligned}
--   |S_{\eta_0,2}(x,\alpha)|\ \le\ & \frac xq(\log x)\Bigl(\log\Bigl(\frac{2UV}{q}+4\Bigr)+4\Bigr)+1.78\Bigl(UV+\frac52q\Bigr)(8+\log q)\log(2x)\\
--   &+\Bigl(0.1\frac{x}{\sqrt q}+0.39\frac{x}{\sqrt{x/q}}\Bigr)\Bigl(\log\frac{x}{UV}\Bigr)\log\frac{Vx}{U}+\Bigl(0.55\frac{x}{\sqrt U}+1.1\frac{x}{\sqrt V}\Bigr)\log\frac xU .
--   \end{aligned}$$
--   Then
--   $$|S_{\eta_0,q_0}(x,\alpha)|\ \le\ \Bigl(0.14\frac{x}{\sqrt q}+0.64\frac{x}{\sqrt{x/q}}+0.15\,x^{4/5}\Bigr)(\log x)(\log x+11.3).$$
--
--   This says that the three constants of Theorem 5.1 that its proof does not support cost nothing downstream: the exponential sum estimate of Theorem 1.3 comes out **unchanged**. The source's own choice $U=\frac14x^{2/5}$, $V=\frac12x^{2/5}$ no longer works — with the doubled second term it overshoots the $0.15\,x^{4/5}$ coefficient — but the balanced choice
--   $$U=V=\tfrac1{10}x^{2/5}$$
--   does, and comfortably. Writing $\ell=\frac{\log x}5\ge9$, the binding inequality becomes $3.305\ell^2-7.955\ell-12.267\ge0$, whose value at $\ell=9$ is $183.8$. The passage from the sifting modulus $2$ to the general modulus $q_0$ is the source's Lemma 4.1, public and proved on the platform as `TaoFivePrimes.smoothedExpSum_modulus_change`.
--
--   **Formalization Note** The minor-arc bound is carried as a hypothesis quantified over all admissible $U,V$, so this statement isolates exactly the content of Section 6 and can be proved independently of Section 5. The power $x^{4/5}$ is the real power `x ^ (4/5 : ℝ)`.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 6 (Proof of Theorem 1.3), run from Theorem 5.1 with the constants its proof yields, at U = V = x^{2/5}/10

import Mathlib
import Definitions.Def_TaoFivePrimes_SmoothedExpSum
import Definitions.Def_TaoFivePrimes_RepresentationCount

open Finset

theorem TaoFivePrimes.exp_sum_estimate_from_theorem51_as_proved
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
          (x / q) * Real.log x * (Real.log (2 * U * V / q + 4) + 4)
            + 1.78 * (U * V + (5 / 2) * q) * (8 + Real.log q) * Real.log (2 * x)
          + (0.1 * x / Real.sqrt q + 0.39 * x / Real.sqrt (x / q))
              * Real.log (x / (U * V)) * Real.log (V * x / U)
          + (0.55 * x / Real.sqrt U + 1.1 * x / Real.sqrt V) * Real.log (x / U)) :
    ‖TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 q₀ x α‖ ≤
      (0.14 * x / Real.sqrt q + 0.64 * x / Real.sqrt (x / q) + 0.15 * x ^ (4 / 5 : ℝ))
        * Real.log x * (Real.log x + 11.3) := by sorry
