-- Prove2me | Theorems.Thm_SpatialDemandEq_Optimal_Supplement_lemma_2
-- name    : SpatialDemandEq.Optimal.Supplement.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T06:37:29.07104+00:00
-- url     : https://prove2.me/theorems/2e235163-1eab-4c64-b478-7e48fc537591
-- title:
--   Lemma 2, p. 9 — the optimal value w̄ of max_a min_k f_k(a_k) over the simplex is finite
-- statement:
--   Let $c > 0$ and $\lambda > 0$, and let $\mu_1,\dots,\mu_K$ be service rates with $\mu_k > 0$ for every $k$ and $\sum_k \mu_k > \lambda$. For each $k$, let $f_k(A) = c/(\mu_k - \lambda A)$ when $\lambda A < \mu_k$ and $f_k(A) = +\infty$ otherwise. Let $\bar w$ be the optimal value of
--   $$\max_{a}\ \min_k f_k(a_k) \qquad \text{subject to } a = (a_1,\dots,a_K) \ge 0,\ \sum_k a_k = 1, \tag{4}$$
--   taken as a supremum in the extended reals. Then
--   $$\bar w < \infty .$$
--
--   In the paper, this finiteness makes the bound $\bar w^*$ a real number, so the box $\mathcal W$ on which the truncated map $\phi$ acts is compact; Theorem 1 uses $\bar w < \bar w^*$.
--
--   **Formalization Note** In the paper's notation $t_k = \mu_k/\lambda$, the hypotheses are $t_k > 0$ and $\sum_k t_k > 1$ (p. 9).
--
--   Differences from the source:
--   - encoding: f_k maps into R̄+ = R+ ∪ {∞}, and w̄ is the optimal value (a max) of (4) → f_k is `EReal`-valued, equal to ⊤ exactly when λA ≥ μ_k, and w̄ is the `EReal` supremum over the simplex; reason: the supremum is the optimal value whether or not it is attained; same instances
--   - reading: the properties f_k(0) > 0, t_k > 0 and Σ_k t_k > 1 with t_k = μ_k/λ (p. 9) → hypotheses 0 < c, 0 < λ, μ_k > 0 for all k and λ < Σ_k μ_k; reason: these are the paper's stated properties of its f_k = c/(μ_k − λA) rewritten in the model's parameters
-- source:
--   Carlsson, Peng & Ryzhov, Demand Equilibria in Spatial Service Systems, SSRN preprint 4794156 (version of 2024-04-14), p. 9, Lemma 2 (problem (4))

import Mathlib
import Definitions.Def_SpatialDemandEq_Optimal_Model
import Definitions.Def_SpatialDemandEq_Optimal_Supplement_Model

namespace SpatialDemandEq.Optimal.Supplement

theorem lemma_2 {K : ℕ} (c lam : ℝ) (hc : 0 < c) (hlam : 0 < lam) (μ : Fin K → ℝ)
    (hμ : ∀ k, 0 < μ k) (hcap : lam < ∑ k, μ k) :
    wbar c lam μ < ⊤ := by sorry

end SpatialDemandEq.Optimal.Supplement
