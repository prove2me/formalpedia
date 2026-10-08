-- Prove2me | Theorems.Thm_TsallisINF_AdvAlpha_lemma_14
-- name    : TsallisINF.AdvAlpha.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:33:45.337441+00:00
-- url     : https://prove2.me/theorems/88262809-bb73-470f-8567-744660a5c9cd
-- title:
--   Lemma 14, p. 32 — (1 − y^{−x})/x is non-increasing in x > 0, tends to log y, and is ≤ min{x^{−1}, log y}
-- statement:
--   Let $y>0$. The function
--   $$
--   x\mapsto\frac{1-y^{-x}}{x},\qquad x>0,
--   $$
--   is non-increasing on $(0,\infty)$, has the limit $\lim_{x\to0^+}(1-y^{-x})/x=\log y$, and therefore satisfies, for every $x>0$,
--   $$
--   \frac{1-y^{-x}}{x}\le\min\{x^{-1},\log y\}.
--   $$
--
--   In the proof of Theorem 3 this compares the factors $\sqrt{(1-K^{\alpha-1})/(1-\alpha)}$ and $\sqrt{(1-T^{-\alpha})/\alpha}$ of the regret bound with $\sqrt{\log K}$, $\sqrt{1/(1-\alpha)}$, $\sqrt{\log T}$ and $\sqrt{1/\alpha}$.
--
--   **Formalization Note** The limit is one-sided, $x\to0^+$, since the page's function is considered for $x>0$; $\log$ is the natural logarithm and $y^{-x}$ is `Real.rpow`.
-- source:
--   Zimmert & Seldin, Tsallis-INF: An Optimal Algorithm for Stochastic and Adversarial Bandits, arXiv:1807.07623v6, p. 32, Lemma 14

import Mathlib

namespace TsallisINF.AdvAlpha

open Filter Topology

theorem lemma_14 (y : ℝ) (hy : 0 < y) :
    AntitoneOn (fun x : ℝ => (1 - y ^ (-x)) / x) (Set.Ioi 0) ∧
      Tendsto (fun x : ℝ => (1 - y ^ (-x)) / x) (𝓝[>] 0) (𝓝 (Real.log y)) ∧
      ∀ x : ℝ, 0 < x → (1 - y ^ (-x)) / x ≤ min x⁻¹ (Real.log y) := by sorry

end TsallisINF.AdvAlpha
