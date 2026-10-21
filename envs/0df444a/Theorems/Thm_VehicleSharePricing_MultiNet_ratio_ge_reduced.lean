-- Prove2me | Theorems.Thm_VehicleSharePricing_MultiNet_ratio_ge_reduced
-- name    : VehicleSharePricing.MultiNet.ratio_ge_reduced
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T04:31:09.410192+00:00
-- url     : https://prove2.me/theorems/fc613efc-7bcd-4e10-84bb-c88113a476a2
-- title:
--   §6, proof of Theorem 4, p. 18 — $R(q^s,\mathbf K^*)/R_s(q^s)\ge\max_{\sum K_c=K}\sum_cp_cK_c/(N_c+K_c-1+M_c)$
-- statement:
--   In the setting of §6 of Benjaafar and Shen ($q^s$ optimal for Problem (2) with $\Delta\ge K$, splitting the locations into connected networks $c$, and $r$ a positive solution of (9)), assume $R_s(q^s)>0$ and let $\mathbf K^*$ be an optimal allocation of the $K$ vehicles for Problem (8). Then for every allocation $(K_c)_c$ of natural numbers with $\sum_cK_c=K$,
--   $$\frac{R(q^s,\mathbf K^*)}{R_s(q^s)}\ \ge\ \sum_c\frac{p_cK_c}{N_c+K_c-1+M_c},$$
--   that is, the performance ratio is at least the maximum of the right-hand side over all feasible allocations.
--
--   This reduces Theorem 4 to an inequality about the numbers $p_c$, $N_c$ and $M_c$ alone.
--
--   **Formalization Note** The paper writes this step for $C=2$ (p. 18) and uses it in the same form in the case $C>2$ (p. 19); it is stated here for any number of networks. A term with $K_c=0$ is $p_c\cdot0/(N_c-1+M_c)=0$. $R_s(q^s)>0$ is added because the ratio divides by $R_s(q^s)$.
-- source:
--   Benjaafar & Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN abstract 3998297 (version of 2023-01-10), p. 18, §6, proof of Theorem 4, case C = 2 ("bounds from below the objective function for every feasible solution")

import Mathlib
import Definitions.Def_VehicleSharePricing_MultiNet_Model

namespace VehicleSharePricing.MultiNet

/-- §6, proof of Theorem 4, p. 18: with `K*` an optimal allocation of Problem (8),
`R(q^s, K*) / R_s(q^s) ≥ ∑_c p_c K_c / (N_c + K_c - 1 + M_c)` for every feasible allocation
`(K_c)`, i.e. `R(q^s, K*) / R_s(q^s)` is at least the maximum of the right side over allocations.
A term with `K_c = 0` is `p_c · 0 / (…) = 0`. -/
theorem ratio_ge_reduced {L ι : Type*} [Fintype L] [DecidableEq L] [Nonempty L] [Fintype ι] [DecidableEq ι]
    (Λ μ : L → L → ℝ) (I : L → L → ℝ → ℝ) (Δ : ℝ) (K : ℕ) (q : L → L → ℝ) (r : L → ℝ)
    (comp : L → ι) (h : SplitStaticSetting Λ μ I Δ K q r comp)
    (hRs : 0 < rewardS Λ I q) (Kstar : ι → ℕ)
    (hKstar : IsOptimalAllocation Λ μ q I r comp K Kstar)
    (k : ι → ℕ) (hk : k ∈ allocations ι K) :
    ∑ c, classWeight Λ q I comp c * (k c : ℝ) /
        ((classSize comp c : ℝ) + (k c : ℝ) - 1 + classWorkload Λ μ q comp c) ≤
      reward Λ μ q I r comp Kstar / rewardS Λ I q := by sorry

end VehicleSharePricing.MultiNet
