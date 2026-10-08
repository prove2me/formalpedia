-- Prove2me | Theorems.Thm_TsallisINF_StoAlpha_lemma_16
-- name    : TsallisINF.StoAlpha.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:38:49.628429+00:00
-- url     : https://prove2.me/theorems/5c8e902f-395f-40fd-b0b3-6a2806a18881
-- title:
--   Lemma 16, p. 33 — $(1-z^{-1+\alpha})/(1-\alpha)\le(\log z)^\alpha$ for $z\ge 1$
-- statement:
--   For every $\alpha\in[0,1)$ and every $z\ge1$,
--   $$\frac{1-z^{-1+\alpha}}{1-\alpha}\le(\log z)^\alpha ,$$
--   with the convention $0^0=1$ at $z=1$, $\alpha=0$.
--
--   The proof of Theorem 4 uses this inequality to show that the learning rate satisfies $\eta_t\xi_i\le\Delta_i/4$ for all $t>T_0$.
--
--   **Formalization Note** The page also allows $\alpha=1$, read as the limit $\lim_{\alpha\to1}\frac{1-z^{-1+\alpha}}{1-\alpha}=\log z\le\log z$, which is trivial and not stated. Real powers are `Real.rpow`, for which $0^0=1$ is the page's convention.
-- source:
--   Zimmert & Seldin, Tsallis-INF: An Optimal Algorithm for Stochastic and Adversarial Bandits, arXiv:1807.07623v6, p. 33, Lemma 16

import Mathlib

namespace TsallisINF.StoAlpha
theorem lemma_16 (α : ℝ) (hα : α ∈ Set.Ico (0 : ℝ) 1) (z : ℝ) (hz : 1 ≤ z) :
    (1 - z ^ (-1 + α)) / (1 - α) ≤ Real.log z ^ α := by sorry
end TsallisINF.StoAlpha
