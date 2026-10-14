-- Prove2me | Theorems.Thm_PeriodicMAB_Lower_fact_2_continuity
-- name    : PeriodicMAB.Lower.fact_2_continuity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:08:28.845673+00:00
-- url     : https://prove2.me/theorems/8ef38d9f-c7b6-4b3d-9937-92c245272166
-- title:
--   Proof of Theorem 3, p. 48, fact 2 — the regret f_π(ν) is continuous on ℰ₂ ∪ ℰ₃ in the metric ℳ, uniformly in π
-- statement:
--   Let $K \ge 2$, let $T$ be the horizon and $T_1, \dots, T_K \ge 1$ integer periods. For a policy $\pi$ and an instance $\nu$ write $f_\pi(\nu) = \mathbb E_\nu[R^\pi_T]$ for the expected regret (1) of $\pi$ on $\nu$ with unit-variance Gaussian rewards.
--
--   Fix $\nu_1 \in \mathcal E_2(T_1) \cup \mathcal E_3(T_1, \dots, T_K)$. Then for every $\varepsilon > 0$ there is $\delta > 0$ such that for every policy $\pi$ and every $\nu_2 \in \mathcal E_2(T_1) \cup \mathcal E_3(T_1, \dots, T_K)$,
--   $$\mathcal M(\nu_1, \nu_2) < \delta \implies |f_\pi(\nu_1) - f_\pi(\nu_2)| < \varepsilon,$$
--   where $\mathcal M$ is the metric (B-48). The same $\delta$ works for all policies.
--
--   This is the second of the two facts from which Theorem 3 follows: the slight perturbation provided by fact 1 changes the regret of any policy only slightly.
--
--   **Formalization Note** $\delta$ is chosen after $\nu_1$ and $\varepsilon$ and before $\pi$ and $\nu_2$ (uniform continuity in $\pi$, as printed). The hypothesis $T_k \ge 1$ is the paper's $T_k \in \mathbb N^+$; without it the metric would ignore an arm. Assumption 3 is not needed and is dropped, which makes the statement stronger.
-- source:
--   Chen, Wang and Wang, Learning and Optimization with Seasonal Patterns, arXiv:2005.08088v4, p. 48, proof of Theorem 3, fact 2 (f_π defined p. 48; proof pp. 48–49)

import Mathlib
import Definitions.Def_BanditPolicy
import Definitions.Def_GaussianBandit
import Definitions.Def_PeriodicMAB_Lower_Model

namespace PeriodicMAB.Lower

open BanditAlgorithm

theorem fact_2_continuity (K T : ℕ) [NeZero K] (Tper : Fin K → ℕ) (hK : 2 ≤ K)
    (hTper : ∀ k, 1 ≤ Tper k) (μ₁ : Fin K → ℕ → ℝ)
    (hμ₁ : InE2 T (Tper 0) μ₁ ∨ InE3 T Tper μ₁) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ (π : BanditPolicy K) (μ₂ : Fin K → ℕ → ℝ),
      (InE2 T (Tper 0) μ₂ ∨ InE3 T Tper μ₂) → instDist Tper μ₁ μ₂ < δ →
        |periodicRegret μ₁ π T - periodicRegret μ₂ π T| < ε := by sorry

end PeriodicMAB.Lower
