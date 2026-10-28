-- Prove2me | Theorems.Thm_PeriodicMAB_Lower_fact_1_dense
-- name    : PeriodicMAB.Lower.fact_1_dense
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:08:25.242197+00:00
-- url     : https://prove2.me/theorems/60d92a86-8e6e-4077-b1bf-90aae1a3b165
-- title:
--   Proof of Theorem 3, p. 48, fact 1 — ℰ₃(T₁,…,T_K) is dense in ℰ₂(T₁) ∪ ℰ₃ under the metric ℳ
-- statement:
--   Let $K \ge 2$, let $T$ be the horizon and let $T_1, \dots, T_K \ge 1$ be integer periods. Let $\nu_1$ be an instance of $\mathcal E_2(T_1)$: unit-variance Gaussian, means in $[0,1]$ on epochs $1, \dots, T$, the first arm of minimum period $T_1$ and all other arms stationary. Then for every $\delta > 0$ there is an instance $\nu_2 \in \mathcal E_3(T_1, \dots, T_K)$ (arm $k$ of minimum period $T_k$, means in $[0,1]$) whose first arm coincides with that of $\nu_1$ and such that
--   $$\mathcal M(\nu_1, \nu_2) < \delta,$$
--   where $\mathcal M(\nu_1,\nu_2) = \big(\sum_{k=1}^K \sum_{p=1}^{T_k} (\mu^{(\nu_1)}_{k,p} - \mu^{(\nu_2)}_{k,p})^2\big)^{1/2}$ is the metric (B-48).
--
--   This is the first of the two facts from which Theorem 3 follows: an instance of $\mathcal E_2(T_1)$ can be perturbed slightly, on the arms other than the first, into an instance with the required periods.
--
--   **Formalization Note** The statement records that the first arm (index $0$) is left unchanged, as in the printed construction ("perturbing its mean rewards for certain arms $k \ge 2$"). The hypothesis $T_k \ge 1$ is the paper's $T_k \in \mathbb N^+$; $K \ge 2$ is the setting of §5.
-- source:
--   Chen, Wang and Wang, Learning and Optimization with Seasonal Patterns, arXiv:2005.08088v4, p. 48, proof of Theorem 3, fact 1 (metric (B-48))

import Mathlib
import Definitions.Def_BanditPolicy
import Definitions.Def_GaussianBandit
import Definitions.Def_PeriodicMAB_Lower_Model

namespace PeriodicMAB.Lower

theorem fact_1_dense (K T : ℕ) [NeZero K] (Tper : Fin K → ℕ) (hK : 2 ≤ K)
    (hTper : ∀ k, 1 ≤ Tper k) (μ₁ : Fin K → ℕ → ℝ) (hμ₁ : InE2 T (Tper 0) μ₁)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ μ₂ : Fin K → ℕ → ℝ, InE3 T Tper μ₂ ∧ μ₂ 0 = μ₁ 0 ∧ instDist Tper μ₁ μ₂ < δ := by sorry

end PeriodicMAB.Lower
