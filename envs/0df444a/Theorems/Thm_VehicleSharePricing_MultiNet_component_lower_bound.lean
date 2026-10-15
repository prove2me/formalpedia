-- Prove2me | Theorems.Thm_VehicleSharePricing_MultiNet_component_lower_bound
-- name    : VehicleSharePricing.MultiNet.component_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:31:16.69715+00:00
-- url     : https://prove2.me/theorems/4dfa80d4-d84a-4cba-90d7-fb86e44b71d9
-- title:
--   §6, proof of Theorem 4, p. 18 — $p_cK_c/(N_c+K_c-1+M_c(1-\alpha(q^s,K_c-1,N_c)))\ge p_cK_c/(N_c+K_c-1+M_c)$
-- statement:
--   In the setting of §6 of Benjaafar and Shen ($q^s$ optimal for Problem (2) with $\Delta\ge K$, splitting the locations into connected networks $c$, and $r$ a positive solution of (9)), let $p_c$ be the share of network $c$ in the fluid reward, $N_c$ its number of locations, $M_c$ its workload, and $\alpha(q^s,K_c,N_c)$ the availability at any of its locations with $K_c$ vehicles. Then for every network $c$ and every $K_c\in\mathbb N$ with $K\ge K_c>0$,
--   $$\frac{p_cK_c}{N_c+K_c-1+M_c\big(1-\alpha(q^s,K_c-1,N_c)\big)}\ \ge\ \frac{p_cK_c}{N_c+K_c-1+M_c}.$$
--
--   Combined with the per-network recursion, it bounds each term of the mixture $\sum_c\alpha(q^s,K_c,N_c)p_c$ from below by a quantity that no longer involves the availabilities.
--
--   **Formalization Note** The paper writes this for the two networks of the case $C=2$; it is stated here for every network. No positivity of $R_s(q^s)$ is assumed: if $R_s(q^s)=0$, then $p_c=0$ and both sides vanish. The inequality uses $p_c\ge0$, which holds because $q^s$ is optimal (switching off a network whose fluid reward is negative keeps $q$ feasible). $K_c-1$ is natural-number subtraction, used only under $K_c>0$.
-- source:
--   Benjaafar & Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN abstract 3998297 (version of 2023-01-10), p. 18, §6, proof of Theorem 4, case C = 2

import Mathlib
import Definitions.Def_VehicleSharePricing_MultiNet_Model

namespace VehicleSharePricing.MultiNet

/-- §6, proof of Theorem 4, p. 18: for every network `c`, every location `i` of it and every
`Kc ∈ ℕ` with `K ≥ Kc > 0`,
`p_c Kc / (N_c + Kc - 1 + M_c (1 - α(q^s, Kc - 1, N_c))) ≥ p_c Kc / (N_c + Kc - 1 + M_c)`. -/
theorem component_lower_bound {L ι : Type*} [Fintype L] [DecidableEq L] [Nonempty L] [Fintype ι] [DecidableEq ι]
    (Λ μ : L → L → ℝ) (I : L → L → ℝ → ℝ) (Δ : ℝ) (K : ℕ) (q : L → L → ℝ) (r : L → ℝ)
    (comp : L → ι) (h : SplitStaticSetting Λ μ I Δ K q r comp)
    (c : ι) (i : ClassLoc comp c) (Kc : ℕ) (hKc0 : 0 < Kc) (hKcK : Kc ≤ K) :
    classWeight Λ q I comp c * (Kc : ℝ) /
        ((classSize comp c : ℝ) + (Kc : ℝ) - 1 + classWorkload Λ μ q comp c) ≤
      classWeight Λ q I comp c * (Kc : ℝ) /
        ((classSize comp c : ℝ) + (Kc : ℝ) - 1 +
          classWorkload Λ μ q comp c * (1 - classAvail Λ μ q r comp c (Kc - 1) i)) := by sorry

end VehicleSharePricing.MultiNet
