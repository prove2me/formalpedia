-- Prove2me | Theorems.Thm_TaoFivePrimes_smoothedExpSum_modulus_change
-- name    : TaoFivePrimes.smoothedExpSum_modulus_change
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-13T20:24:29.314987+00:00
-- url     : https://prove2.me/theorems/1ad7adb1-dc4e-4ba9-bc8c-20391c09af92
-- title:
--   Tao Lemma 4.1: the smoothed prime exponential sum barely depends on the sifting modulus
-- statement:
--   For a cutoff $\eta$, a modulus $q_0$, a scale $x$ and a frequency $\alpha$, write
--
--   $$S_{\eta,q_0}(x,\alpha)\;=\;\sum_{n}\Lambda(n)\,e(\alpha n)\,\mathbf 1_{(n,q_0)=1}\,\eta\!\left(\frac nx\right),$$
--
--   where $\Lambda$ is the von Mangoldt function and $e(t)=e^{2\pi i t}$.
--
--   The sum barely depends on the sifting modulus: if $\eta$ vanishes on $(1,\infty)$ and $|\eta|\le M$ everywhere, then for $x\ge1$ and $q_0\ge1$
--
--   $$\bigl|S_{\eta,q_0}(x,\alpha)-S_{\eta,1}(x,\alpha)\bigr|\;\le\;\omega(q_0)\,M\,\log x ,$$
--
--   where $\omega(q_0)$ is the number of distinct prime factors of $q_0$.
--
--   The point of the lemma is that the modulus $q_0$ is only of minor technical importance and can be removed at negligible cost; in the source it is what justifies ignoring $q_0$ at a first reading. When every prime factor of $q_0$ is at most $\sqrt x$ it specialises, via an explicit bound on $\pi(\sqrt x)$, to an error of size $2.52\sqrt x\,M$.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 4, Lemma 4.1

import Mathlib
import Definitions.Def_TaoFivePrimes_SmoothedExpSum

theorem TaoFivePrimes.smoothedExpSum_modulus_change
    (eta : ℝ → ℝ) (M : ℝ) (q₀ : ℕ) (x alpha : ℝ)
    (hq : 0 < q₀) (hx : 1 ≤ x)
    (hM : ∀ t : ℝ, |eta t| ≤ M)
    (hsupp : ∀ t : ℝ, 1 < t → eta t = 0) :
    ‖TaoFivePrimes.smoothedExpSum eta q₀ x alpha
        - TaoFivePrimes.smoothedExpSum eta 1 x alpha‖
      ≤ (q₀.primeFactors.card : ℝ) * M * Real.log x := by sorry
