-- Prove2me | Theorems.Thm_VehicleSharePricing_MultiNet_case_general
-- name    : VehicleSharePricing.MultiNet.case_general
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:29:42.57515+00:00
-- url     : https://prove2.me/theorems/c48666b6-990a-4b63-9c92-3f151c198aea
-- title:
--   §6, proof of Theorem 4, p. 19 — case $C>2$: $\max_{\sum K_c=K}\sum_cp_cK_c/(N_c+K_c-1+M_c)\ge K/(N+K-1+M)$
-- statement:
--   Let $\iota$ be a finite index set of networks. For each $c\in\iota$ let $p_c\ge0$ with $\sum_cp_c=1$, let $N_c\ge1$ be a natural number and $M_c\ge0$ a real number, and put $N=\sum_cN_c$, $M=\sum_cM_c$. Then for every $K\in\mathbb N$ there is an allocation $(K_c)_{c\in\iota}$ of natural numbers with $\sum_cK_c=K$ and
--   $$\sum_c\frac{p_cK_c}{N_c+K_c-1+M_c}\ \ge\ \frac{K}{N+K-1+M}.$$
--   Equivalently, $\max_{\sum_cK_c=K}\sum_cp_cK_c/(N_c+K_c-1+M_c)\ge K/(N+K-1+M)$.
--
--   This is the inequality the paper establishes in the case $C>2$ of Theorem 4 by induction on the number of networks, starting from the case $C=2$. Together with the reduction $R(q^s,\mathbf K^*)/R_s(q^s)\ge\max_{\sum K_c=K}\sum_cp_cK_c/(N_c+K_c-1+M_c)$ it gives Theorem 4.
--
--   **Formalization Note** The statement covers every number of networks $C=|\iota|\ge1$ (the condition $\sum_cp_c=1$ forces $\iota\neq\emptyset$); $C=1$ is immediate and $C=2$ is the previous milestone. A summand with $K_c=0$ is $p_c\cdot0/(N_c-1+M_c)=0$. At $K=0$ the right-hand side is $0$.
-- source:
--   Benjaafar & Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN abstract 3998297 (version of 2023-01-10), p. 19, §6, proof of Theorem 4, case C > 2

import Mathlib

namespace VehicleSharePricing.MultiNet

/-- §6, proof of Theorem 4, p. 19 (the case `C > 2`, reduced form, concluded by induction on the
number of networks): for any finite family of networks `c ∈ ι` with weights `p_c ≥ 0`,
`∑_c p_c = 1`, location counts `N_c ≥ 1` and workloads `M_c ≥ 0`, with `N = ∑_c N_c` and
`M = ∑_c M_c`, some allocation `∑_c K_c = K` satisfies
`∑_c p_c K_c / (N_c + K_c - 1 + M_c) ≥ K / (N + K - 1 + M)`.
A summand with `K_c = 0` is `p_c · 0 / (…) = 0`. -/
theorem case_general {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp0 : ∀ c, 0 ≤ p c)
    (hp1 : ∑ c, p c = 1) (N : ι → ℕ) (hN : ∀ c, 1 ≤ N c) (M : ι → ℝ) (hM : ∀ c, 0 ≤ M c)
    (K : ℕ) :
    ∃ k : ι → ℕ, ∑ c, k c = K ∧
      (K : ℝ) / ((∑ c, (N c : ℝ)) + (K : ℝ) - 1 + ∑ c, M c) ≤
        ∑ c, p c * (k c : ℝ) / ((N c : ℝ) + (k c : ℝ) - 1 + M c) := by sorry

end VehicleSharePricing.MultiNet
