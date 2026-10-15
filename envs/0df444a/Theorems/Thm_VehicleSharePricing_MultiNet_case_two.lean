-- Prove2me | Theorems.Thm_VehicleSharePricing_MultiNet_case_two
-- name    : VehicleSharePricing.MultiNet.case_two
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:29:44.754839+00:00
-- url     : https://prove2.me/theorems/c2026eee-a4bd-451b-861e-389f1039ebf3
-- title:
--   §6, proof of Theorem 4, pp. 18–19 — case $C=2$: $\max_{K_1+K_2=K}\sum_{i=1}^2p_iK_i/(N_i+K_i-1+M_i)\ge K/(N+K-1+M)$
-- statement:
--   Let $p_1,p_2\ge0$ with $p_1+p_2=1$, let $N_1,N_2\ge1$ be natural numbers, $M_1,M_2\ge0$ real numbers, $N=N_1+N_2$, $M=M_1+M_2$, and $K\in\mathbb N$. Then there are natural numbers $K_1,K_2$ with $K_1+K_2=K$ and
--   $$\frac{p_1K_1}{N_1+K_1-1+M_1}+\frac{p_2K_2}{N_2+K_2-1+M_2}\ \ge\ \frac{K}{N+K-1+M}.$$
--   Equivalently,
--   $$\max_{K_1,K_2\ge0,\ K_1+K_2=K}\left(\frac{p_1K_1}{N_1+K_1-1+M_1}+\frac{p_2K_2}{N_2+K_2-1+M_2}\right)\ \ge\ \frac{K}{N+K-1+M}.$$
--
--   With $p_i$, $N_i$, $M_i$ the reward share, number of locations and workload of the two networks, this is the case $C=2$ of Theorem 4 after the reduction of p. 18; the paper concludes it as "$R(q^s,\mathbf K^*)/R_s(q^s)\ge K/(N+K-1+M)$ is true when $C=2$".
--
--   **Formalization Note** The maximum over the finite set of allocations is written as the existence of an allocation achieving the bound. A summand with $K_i=0$ is $p_i\cdot0/(N_i-1+M_i)=0$; when $K_i\ge1$ its denominator is at least $1$. At $K=0$ the right-hand side is $0$.
-- source:
--   Benjaafar & Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN abstract 3998297 (version of 2023-01-10), pp. 18–19, §6, proof of Theorem 4, case C = 2

import Mathlib

namespace VehicleSharePricing.MultiNet

/-- §6, proof of Theorem 4, pp. 18–19 (the case `C = 2`, reduced form): for weights
`p₁, p₂ ≥ 0` with `p₁ + p₂ = 1`, location counts `N₁, N₂ ≥ 1` and workloads `M₁, M₂ ≥ 0`, with
`N = N₁ + N₂` and `M = M₁ + M₂`,
`max_{K₁,K₂ ≥ 0, K₁+K₂=K} (p₁K₁/(N₁+K₁-1+M₁) + p₂K₂/(N₂+K₂-1+M₂)) ≥ K/(N+K-1+M)`.
A summand with `K_i = 0` is `p_i · 0 / (…) = 0`. -/
theorem case_two (p₁ p₂ : ℝ) (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp : p₁ + p₂ = 1)
    (N₁ N₂ : ℕ) (hN₁ : 1 ≤ N₁) (hN₂ : 1 ≤ N₂) (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (K : ℕ) :
    ∃ K₁ K₂ : ℕ, K₁ + K₂ = K ∧
      (K : ℝ) / ((N₁ : ℝ) + (N₂ : ℝ) + (K : ℝ) - 1 + (M₁ + M₂)) ≤
        p₁ * (K₁ : ℝ) / ((N₁ : ℝ) + (K₁ : ℝ) - 1 + M₁) +
          p₂ * (K₂ : ℝ) / ((N₂ : ℝ) + (K₂ : ℝ) - 1 + M₂) := by sorry

end VehicleSharePricing.MultiNet
