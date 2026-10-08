-- Prove2me | Theorems.Thm_TsallisINF_AdvAlpha_simplex_max
-- name    : TsallisINF.AdvAlpha.simplex_max
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:33:45.671653+00:00
-- url     : https://prove2.me/theorems/f093d34d-7883-424b-9afe-5b3f781feda8
-- title:
--   §7.3, p. 24 — max over the simplex of Σ_i z_i^{1−α} is K^α
-- statement:
--   Let $K\ge1$ and $\alpha\in(0,1)$, and let $\Delta^{K-1}=\{z\in\mathbb R^K: z_i\ge0,\ \sum_i z_i=1\}$ be the probability simplex. Then
--   $$
--   \max_{z\in\Delta^{K-1}}\sum_{i=1}^K z_i^{1-\alpha}=K^\alpha,
--   $$
--   that is, $K^\alpha$ is attained on the simplex and is an upper bound for $\sum_i z_i^{1-\alpha}$ there.
--
--   In the proof of Theorem 3 this turns the stability bound of Lemma 11 into $\big(\sum_{t=1}^T\eta_t/2\big)K^\alpha$.
--
--   **Formalization Note** The maximum is stated with `IsGreatest` on the image of the simplex, so both attainment and the upper bound are asserted. Powers are `Real.rpow` with nonnegative base.
-- source:
--   Zimmert & Seldin, Tsallis-INF: An Optimal Algorithm for Stochastic and Adversarial Bandits, arXiv:1807.07623v6, p. 24, proof of Theorem 3 (second display line)

import Mathlib

namespace TsallisINF.AdvAlpha

theorem simplex_max {K : ℕ} (hK : 0 < K) (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    IsGreatest ((fun z : Fin K → ℝ => ∑ i, z i ^ (1 - α)) '' stdSimplex ℝ (Fin K))
      ((K : ℝ) ^ α) := by sorry

end TsallisINF.AdvAlpha
