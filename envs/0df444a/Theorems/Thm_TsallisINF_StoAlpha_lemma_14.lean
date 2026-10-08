-- Prove2me | Theorems.Thm_TsallisINF_StoAlpha_lemma_14
-- name    : TsallisINF.StoAlpha.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:38:22.480685+00:00
-- url     : https://prove2.me/theorems/3e95e910-58eb-431b-b4a2-551097201c18
-- title:
--   Lemma 14, p. 32 — $(1-y^{-x})/x$ is non-increasing in $x>0$ with limit $\log y$, hence at most $\min\{x^{-1},\log y\}$
-- statement:
--   Let $y>0$. The function $x\mapsto\frac{1-y^{-x}}{x}$ is non-increasing on $(0,\infty)$, and
--   $$\lim_{x\to0^+}\frac{1-y^{-x}}{x}=\log y .$$
--   Consequently, for every $x>0$,
--   $$\frac{1-y^{-x}}{x}\le\min\{x^{-1},\log y\}.$$
--
--   The inequality turns the learning-rate factors $(1-T^{-\alpha})/\alpha$ and $(1-T^{-1+\alpha})/(1-\alpha)$ into $\min\{1/\alpha,\log T\}$ and $\min\{1/(1-\alpha),\log T\}$.
--
--   **Formalization Note** $\log$ is the natural logarithm and $y^{-x}$ is the real power; the limit is one-sided ($x\to0^+$), as the function is considered for $x>0$.
-- source:
--   Zimmert & Seldin, Tsallis-INF: An Optimal Algorithm for Stochastic and Adversarial Bandits, arXiv:1807.07623v6, p. 32, Lemma 14

import Mathlib

open Filter Topology

namespace TsallisINF.StoAlpha
theorem lemma_14 (y : ℝ) (hy : 0 < y) :
    AntitoneOn (fun x : ℝ => (1 - y ^ (-x)) / x) (Set.Ioi 0) ∧
      Tendsto (fun x : ℝ => (1 - y ^ (-x)) / x) (𝓝[>] 0) (𝓝 (Real.log y)) ∧
      ∀ x : ℝ, 0 < x → (1 - y ^ (-x)) / x ≤ min x⁻¹ (Real.log y) := by sorry
end TsallisINF.StoAlpha
