-- Prove2me | Theorems.Thm_TTSABilevel_SC_lemma_11
-- name    : TTSABilevel.SC.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:30:16.445237+00:00
-- url     : https://prove2.me/theorems/8cd9723c-8d3a-4654-a2e5-940206ad7d01
-- title:
--   Lemma 11 (108): coupling of two contraction products
-- statement:
--   Let $a,b>0$ and let $(\gamma_j)$ and $(\rho_j)$ be nonnegative, nonincreasing sequences such that $2a\gamma_j\le b\rho_j$ for all $j$ and $\rho_0<1/b$. Then for every $k\ge0$,
--
--   $$
--   \sum_{j=0}^k\gamma_j\prod_{\ell=j+1}^k(1-a\gamma_\ell)
--   \prod_{i=0}^j(1-b\rho_i)
--   \le\frac1a\prod_{\ell=0}^k(1-a\gamma_\ell).
--   $$
--
--   This deterministic inequality controls the coupled product term in the outer-error estimate.
-- source:
--   Hong, Wai, Wang & Yang, A Two-Timescale Stochastic Algorithm Framework for Bilevel Optimization: Complexity Analysis and Application to Actor-Critic, arXiv:2007.05170v4, p. 34, App. E, Lemma 11 (108)

import Mathlib

namespace TTSABilevel.SC

theorem lemma_11 (a b : ℝ) (γ ρ : ℕ → ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hγmono : Antitone γ) (hρmono : Antitone ρ)
    (hγnonneg : ∀ j, 0 ≤ γ j) (hρnonneg : ∀ j, 0 ≤ ρ j)
    (hscale : ∀ j, 2 * a * γ j ≤ b * ρ j)
    (hfirst : ρ 0 < 1 / b) :
    ∀ k : ℕ,
      (∑ j ∈ Finset.range (k + 1),
        γ j * (∏ ℓ ∈ Finset.Icc (j + 1) k, (1 - γ ℓ * a)) *
          (∏ i ∈ Finset.range (j + 1), (1 - ρ i * b))) ≤
        1 / a * (∏ ℓ ∈ Finset.range (k + 1), (1 - γ ℓ * a)) := by sorry

end TTSABilevel.SC
