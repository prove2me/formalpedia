-- Prove2me | Theorems.Thm_VehicleSharePricing_MultiNet_ratio_mixture
-- name    : VehicleSharePricing.MultiNet.ratio_mixture
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:31:08.449824+00:00
-- url     : https://prove2.me/theorems/8c4cb41c-f411-47ed-a0ec-e60e6194a7bf
-- title:
--   §6, proof of Theorem 4, p. 18 — $R(q^s,\mathbf K)/R_s(q^s)=\sum_c\alpha(q^s,K_c,N_c)\,p_c$ with $\sum_cp_c=1$
-- statement:
--   In the setting of §6 of Benjaafar and Shen ($q^s$ optimal for Problem (2) with $\Delta\ge K$, splitting the locations into connected networks $c$, and $r$ a positive solution of (9)), assume $R_s(q^s)>0$. Let $\mathbf K=(K_c)_c$ be any allocation of vehicles to the networks, and for each network $c$ pick any location $i_c\in\mathcal N_c$. Write $\alpha(q^s,K_c,N_c)$ for the availability at $i_c$ when network $c$ holds $K_c$ vehicles, and
--   $$p_c=\frac{\sum_{(i,j)\in\mathcal A_c}q^s_{ij}\Lambda_{ij}I_{ij}(q^s_{ij})}{\sum_{(i,j)\in\mathcal A}q^s_{ij}\Lambda_{ij}I_{ij}(q^s_{ij})}.$$
--   Then
--   $$\frac{R(q^s,\mathbf K)}{R_s(q^s)}=\sum_c\alpha(q^s,K_c,N_c)\,p_c\qquad\text{and}\qquad\sum_cp_c=1.$$
--
--   The identity rewrites the performance ratio as a mixture of the per-network availabilities, with weights the networks' shares of the fluid reward; the proof of Theorem 4 bounds each availability separately.
--
--   **Formalization Note** The paper states the identity for the optimal allocation $\mathbf K^*$; it is stated here for every allocation, which contains that case. The choice of representative $i_c$ does not matter, since availability is the same at every location of a network. $R_s(q^s)>0$ is added because the ratio and $p_c$ divide by $R_s(q^s)$. The sums over $\mathcal A_c$ omit the pairs joining two different networks, whose accepted demand is zero.
-- source:
--   Benjaafar & Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN abstract 3998297 (version of 2023-01-10), p. 18, §6, proof of Theorem 4 (rewriting of R(q^s,K*)/R_s(q^s), definition of p_c)

import Mathlib
import Definitions.Def_VehicleSharePricing_MultiNet_Model

namespace VehicleSharePricing.MultiNet

/-- §6, proof of Theorem 4, p. 18: for every allocation `Kv` of vehicles to the networks,
`R(q^s, Kv) / R_s(q^s) = ∑_c α(q^s, Kv_c, N_c) p_c` and `∑_c p_c = 1`, where
`α(q^s, Kv_c, N_c)` is the availability at any location `rep c` of network `c`. -/
theorem ratio_mixture {L ι : Type*} [Fintype L] [DecidableEq L] [Nonempty L] [Fintype ι] [DecidableEq ι]
    (Λ μ : L → L → ℝ) (I : L → L → ℝ → ℝ) (Δ : ℝ) (K : ℕ) (q : L → L → ℝ) (r : L → ℝ)
    (comp : L → ι) (h : SplitStaticSetting Λ μ I Δ K q r comp)
    (hRs : 0 < rewardS Λ I q) (Kv : ι → ℕ) (rep : ι → L) (hrep : ∀ c, comp (rep c) = c) :
    reward Λ μ q I r comp Kv / rewardS Λ I q =
        ∑ c, classAvail Λ μ q r comp c (Kv c) ⟨rep c, hrep c⟩ * classWeight Λ q I comp c ∧
      ∑ c, classWeight Λ q I comp c = 1 := by sorry

end VehicleSharePricing.MultiNet
