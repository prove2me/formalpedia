-- Prove2me | Theorems.Thm_VehShare_MultiNet_two_network_bound
-- name    : VehShare.MultiNet.two_network_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T04:06:25.565193+00:00
-- url     : https://prove2.me/theorems/368060d2-7d50-4fd8-bacf-7e40e8b45423
-- title:
--   Case $C=2$: some split attains $(w_1+w_2)K/(N+K-1+M)$
-- statement:
--   Let $w_1,w_2\ge0$ be weights, $N_1,N_2\ge1$ integers, $M_1,M_2\ge0$ reals and $K\ge0$ an integer. Then some split $K=K_1+K_2$ with $K_1,K_2\ge0$ satisfies
--
--   $$
--   \frac{(w_1+w_2)K}{N_1+N_2+K-1+M_1+M_2}\le\frac{w_1K_1}{N_1+K_1-1+M_1}+\frac{w_2K_2}{N_2+K_2-1+M_2}.
--   $$
--
--   With $w_c=p_c$ ($p_1+p_2=1$) the network shares of the fluid reward, the right side is the lower bound on $R(q^s,K)/R_s(q^s)$ obtained from the availability bound, and the paper's chain on p. 19 (an average over splits with the Chu–Vandermonde weights) shows that its maximum is at least $K/(N+K-1+M)$: "Hence, $R(q^s,K^*)/R_s(q^s)\ge K/(N+K-1+M)$ is true when $C=2$."
--
--   **Formalization Note** $K_2=K-K_1$ is computed in the reals. A denominator vanishes only when $N_c=1$, $K_c=0$, $M_c=0$, where the numerator is $0$ as well; Lean's $0/0=0$ is the paper's value. The paper's chain writes $p$, $1-p$ for $p_1$, $p_2$ and divides by $\binom{K+T-1}{T-1}$ where $\binom{K+T-1}{K}$ is meant; neither affects this statement.
--
--   Differences from the source:
--   - reading: the C = 2 claim R(q^s,K*)/Rs(q^s) ≥ K/(N+K−1+M), via the lower bound max_{K1+K2=K}(p1K1/(N1+K1−1+M1) + p2K2/(N2+K2−1+M2)) → the inequality for that maximum: some K1 ≤ K with (w1+w2)K/(N1+N2+K−1+M1+M2) ≤ w1K1/(N1+K1−1+M1) + w2(K−K1)/(N2+K−K1−1+M2); reason: the chain on p. 19 proves exactly this bound on the maximum; the reduction from R(q^s,K*)/Rs(q^s) to the maximum is the availability lower bound, and the model-level bound for any number of networks is a separate milestone
--   - generalization: weights p1, p2 ≥ 0 with p1 + p2 = 1 → weights w1, w2 ≥ 0 and the bound (w1+w2)K/(…); reason: dividing by w1 + w2 > 0 gives the paper's form; w1 = w2 = 0 is trivial
--   - generalization: N_i the number of locations and M_i the workload of network i → any integers N1, N2 ≥ 1 and reals M1, M2 ≥ 0; reason: only these properties enter the inequality
-- source:
--   Benjaafar, Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN 3998297 (version of 2023-01-10), https://ssrn.com/abstract=3998297, proof of Theorem 4, case C = 2, pp. 18–19

import Mathlib

namespace VehShare.MultiNet

/-- **The case of two networks.**
Benjaafar, Shen, *Pricing in On-Demand (and One-Way) Vehicle Sharing Networks*, SSRN 3998297
(version of 2023-01-10), proof of Theorem 4, case `C = 2`, pp. 18–19: "`max_{K₁,K₂≥0,K₁+K₂=K} (p₁K₁/(N₁+K₁−1+M₁) +
p₂K₂/(N₂+K₂−1+M₂)) ≥ ... = K/(K+T−1)`. Hence, `R(q^s,K*)/R_s(q^s) ≥ K/(N+K−1+M)` is true when
`C = 2`."

For weights `w₁, w₂ ≥ 0`, integers `N₁, N₂ ≥ 1`, reals `M₁, M₂ ≥ 0` and `K ∈ ℕ`, some split
`K = K₁ + K₂` satisfies
`(w₁ + w₂) K / (N₁ + N₂ + K − 1 + M₁ + M₂) ≤ w₁K₁/(N₁ + K₁ − 1 + M₁) + w₂K₂/(N₂ + K₂ − 1 + M₂)`.

**Formalization Note.** Weights `w_c ≥ 0` in place of the paper's `p₁ + p₂ = 1` (scaling gives the
paper's form; a generalization). `K₂ = K − K₁` is computed in `ℝ`. A denominator vanishes only when
`N_c = 1`, `K_c = 0`, `M_c = 0`, where the numerator is 0 too and Lean's `0/0 = 0` is the paper's 0. -/
theorem two_network_bound (w₁ w₂ : ℝ) (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (N₁ N₂ : ℕ)
    (hN₁ : 1 ≤ N₁) (hN₂ : 1 ≤ N₂) (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (K : ℕ) :
    ∃ K₁ : ℕ, K₁ ≤ K ∧
      (w₁ + w₂) * K / ((N₁ : ℝ) + N₂ + K - 1 + (M₁ + M₂)) ≤
        w₁ * K₁ / ((N₁ : ℝ) + K₁ - 1 + M₁) +
          w₂ * ((K : ℝ) - K₁) / ((N₂ : ℝ) + ((K : ℝ) - K₁) - 1 + M₂) := by sorry

end VehShare.MultiNet
