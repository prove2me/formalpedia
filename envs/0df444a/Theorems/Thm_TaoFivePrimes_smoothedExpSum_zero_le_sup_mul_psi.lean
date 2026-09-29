-- Prove2me | Theorems.Thm_TaoFivePrimes_smoothedExpSum_zero_le_sup_mul_psi
-- name    : TaoFivePrimes.smoothedExpSum_zero_le_sup_mul_psi
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-13T21:13:52.103663+00:00
-- url     : https://prove2.me/theorems/0d917a4c-2611-4eb1-9a92-2028591e37a6
-- title:
--   Tao Lemma 4.3: the smoothed prime sum at zero frequency is at most $\|\eta\|_\infty\,\psi(x)$
-- statement:
--   For a cutoff $\eta$, a modulus $q_0$, a scale $x$ and a frequency $\alpha$, write
--
--   $$S_{\eta,q_0}(x,\alpha)\;=\;\sum_{n}\Lambda(n)\,e(\alpha n)\,\mathbf 1_{(n,q_0)=1}\,\eta\!\left(\frac nx\right),$$
--
--   where $\Lambda$ is the von Mangoldt function and $e(t)=e^{2\pi i t}$.
--
--   Let $\eta$ vanish on $(1,\infty)$ with $|\eta|\le M$ everywhere, and let $x\ge1$. Then
--
--   $$\bigl|S_{\eta,q_0}(x,0)\bigr|\;\le\;M\,\psi(x),\qquad \psi(x)=\sum_{n\le x}\Lambda(n).$$
--
--   This is the first display of Lemma 4.3, the trivial upper bound on the total mass. Combined with the explicit Chebyshev estimate $\psi(x)\le1.04\,x$ of Rosser and Schoenfeld it gives the bound $S_{\eta,q_0}(x,0)\le1.04\,\|\eta\|_{L^\infty}x$ that the source uses repeatedly, in particular in Corollary 4.9.
--
--   **Formalization Note** $\psi$ is the second Chebyshev function of the ambient library, $\psi(x)=\sum_{0<n\le\lfloor x\rfloor}\Lambda(n)$.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 4, Lemma 4.3, equation (4.3)

import Mathlib
import Definitions.Def_TaoFivePrimes_SmoothedExpSum

theorem TaoFivePrimes.smoothedExpSum_zero_le_sup_mul_psi
    (eta : ℝ → ℝ) (M : ℝ) (q₀ : ℕ) (x : ℝ) (hx : 1 ≤ x)
    (hM : ∀ t : ℝ, |eta t| ≤ M)
    (hsupp : ∀ t : ℝ, 1 < t → eta t = 0) :
    ‖TaoFivePrimes.smoothedExpSum eta q₀ x 0‖ ≤ M * Chebyshev.psi x := by sorry
