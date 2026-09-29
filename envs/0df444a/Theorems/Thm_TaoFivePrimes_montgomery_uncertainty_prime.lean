-- Prove2me | Theorems.Thm_TaoFivePrimes_montgomery_uncertainty_prime
-- name    : TaoFivePrimes.montgomery_uncertainty_prime
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-13T21:48:42.452681+00:00
-- url     : https://prove2.me/theorems/3f6b74bf-cd73-43e2-928b-01ad2868814a
-- title:
--   Tao Lemma 4.4 (prime modulus): Montgomery's uncertainty principle
-- statement:
--   For a cutoff $\eta$, a modulus $q_0$, a scale $x$ and a frequency $\alpha$, write
--
--   $$S_{\eta,q_0}(x,\alpha)\;=\;\sum_{n}\Lambda(n)\,e(\alpha n)\,\mathbf 1_{(n,q_0)=1}\,\eta\!\left(\frac nx\right),$$
--
--   where $\Lambda$ is the von Mangoldt function and $e(t)=e^{2\pi i t}$.
--
--   Let $p$ be a prime dividing the sifting modulus $q_0$, let $x\ge1$, and let $\eta$ vanish on $(1,\infty)$. Then
--
--   $$\sum_{a=1}^{p-1}\Bigl|S_{\eta,q_0}\Bigl(x,\alpha+\frac ap\Bigr)\Bigr|^{2}\;\ge\;\frac{1}{p-1}\,\bigl|S_{\eta,q_0}(x,\alpha)\bigr|^{2} .$$
--
--   This is the case $q_0=p$ of Lemma 4.4, whose general form carries the factor $\mu(q_0)^2/\varphi(q_0)$.
--
--   The inequality says that the mass of a prime-supported exponential sum cannot concentrate at a single frequency: shifting by the $p-1$ nonzero fractions $a/p$ must recover a definite proportion of it. It is what drives the local $L^2$ estimate (Lemma 4.6) and hence Corollary 4.7, the large-sieve upper bound on the major arc. Its degenerate case $p=2$ is the anti-symmetry (4.6).
--
--   **Formalization Note** The inequality is stated in the cleared form $|S_{\eta,q_0}(x,\alpha)|^{2}\le(p-1)\sum_{a}|S_{\eta,q_0}(x,\alpha+a/p)|^{2}$, which avoids dividing by $\varphi(p)$.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 4, Lemma 4.4 (Montgomery's uncertainty principle), the case of a prime modulus

import Mathlib
import Definitions.Def_TaoFivePrimes_SmoothedExpSum

theorem TaoFivePrimes.montgomery_uncertainty_prime
    (eta : ℝ → ℝ) (q p : ℕ) (hp : p.Prime) (hpq : p ∣ q) (x alpha : ℝ)
    (hx : 1 ≤ x) (hsupp : ∀ t : ℝ, 1 < t → eta t = 0) :
    ‖TaoFivePrimes.smoothedExpSum eta q x alpha‖ ^ 2
      ≤ ((p : ℝ) - 1) * ∑ a ∈ Finset.Ico 1 p,
          ‖TaoFivePrimes.smoothedExpSum eta q x (alpha + (a : ℝ) / p)‖ ^ 2 := by sorry
