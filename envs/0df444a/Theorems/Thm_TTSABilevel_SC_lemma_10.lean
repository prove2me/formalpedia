-- Prove2me | Theorems.Thm_TTSABilevel_SC_lemma_10
-- name    : TTSABilevel.SC.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:30:13.94817+00:00
-- url     : https://prove2.me/theorems/67f9bd0e-14c2-4d47-b0a6-7266aec596b0
-- title:
--   Lemma 10 (107): weighted sum of contraction products
-- statement:
--   Let $1<q\le2$, $a>0$, and let $(\gamma_j)_{j\ge0}$ be a nonnegative, nonincreasing sequence with $\gamma_0<1/(2a)$. Suppose the consecutive terms satisfy the ratio condition of Lemma 10. Then for every $k\ge0$,
--
--   $$
--   \sum_{j=0}^{k}\gamma_j^q\prod_{\ell=j+1}^{k}(1-a\gamma_\ell)
--   \le \frac{2}{a}\gamma_k^{q-1}.
--   $$
--
--   This deterministic estimate converts a sum of decaying, step-weighted terms into the current step size. The ratio condition is expressed by multiplication so it remains meaningful when a term is zero.
-- source:
--   Hong, Wai, Wang & Yang, A Two-Timescale Stochastic Algorithm Framework for Bilevel Optimization: Complexity Analysis and Application to Actor-Critic, arXiv:2007.05170v4, p. 34, App. E, Lemma 10 (107)

import Mathlib

namespace TTSABilevel.SC

theorem lemma_10 (q a : ℝ) (γ : ℕ → ℝ)
    (hq1 : 1 < q) (hq2 : q ≤ 2) (ha : 0 < a)
    (hmono : Antitone γ) (hnonneg : ∀ j, 0 ≤ γ j)
    (hfirst : γ 0 < 1 / (2 * a))
    (hratio : ∀ ℓ, 1 ≤ ℓ → γ (ℓ - 1) ≤ (1 + a / (2 * (q - 1)) * γ ℓ) * γ ℓ) :
    ∀ k : ℕ,
      (∑ j ∈ Finset.range (k + 1),
        (γ j) ^ q * ∏ ℓ ∈ Finset.Icc (j + 1) k, (1 - γ ℓ * a)) ≤
        2 / a * (γ k) ^ (q - 1) := by sorry

end TTSABilevel.SC
