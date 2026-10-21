-- Prove2me | Theorems.Thm_VehicleSharePricing_MultiNet_theorem_4
-- name    : VehicleSharePricing.MultiNet.theorem_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T04:31:09.01693+00:00
-- url     : https://prove2.me/theorems/cfa2f0f6-325e-436e-a8ec-cf60aca33bca
-- title:
--   Theorem 4, p. 18 (static half) — with split networks and optimal allocation $\mathbf K^*$, $R(q^s,\mathbf K^*)/R_s(q^s)\ge K/(N+K-1+\Lambda/\mu)$
-- statement:
--   Consider the vehicle-sharing network of Benjaafar and Shen with $N$ locations and $K$ vehicles: demand rates $\Lambda_{ij}\ge0$ with $\mathcal A=\{(i,j):\Lambda_{ij}>0\}$ strongly connected, travel rates $\mu_{ij}>0$ on $\mathcal A$, and rewards $I_{ij}$ with $q\mapsto qI_{ij}(q)$ concave on $[0,1]$. Let $\Delta\ge K$ and let $q^s$ be an optimal solution of the fluid Problem (2), with value $R_s(q^s)>0$. Suppose $q^s$ splits the locations into connected networks $c$ (§6): accepted demand $\Lambda_{ij}q^s_{ij}>0$ only joins locations of the same network, and within each network the accepted demand is strongly connected. Let $r$ be a positive solution of the traffic equations (9), and let $\mathbf K^*$ be an optimal allocation of the $K$ vehicles to the networks (Problem (8)), with $R(q^s,\mathbf K^*)$ the resulting expected reward rate (3). Then
--   $$\frac{R(q^s,\mathbf K^*)}{R_s(q^s)}\ \ge\ \frac{K}{N+K-1+\Lambda/\mu},\qquad\text{where }\Lambda=\sum_{(i,j)\in\mathcal A}\Lambda_{ij},\ \ \frac1\mu=\sum_{(i,j)\in\mathcal A}\frac{\Lambda_{ij}}{\Lambda\mu_{ij}}.$$
--
--   The guarantee of Theorem 1 for strongly connected static policies thus survives when the optimal static policy disconnects the network, provided the vehicles are allocated optimally among the pieces.
--
--   **Scope: the static half.** The paper's Theorem 4 reads $R(q^s,\mathbf K^*)/R(q^*)\ge R(q^s,\mathbf K^*)/R_s(q^s)\ge K/(N+K-1+\Lambda/\mu)$, where $R(q^*)$ is the reward of an optimal dynamic (state-dependent) policy. The first inequality is Proposition 1 ($R(q^*)\le R_s(q^s)$, p. 6), whose proof needs the stationary law of the network under an arbitrary state-dependent policy; it is not part of this statement, and no dynamic policy appears in it. This statement implies the paper's theorem once Proposition 1 is available.
--
--   **Formalization Note** $R_s(q^s)>0$ is added because the ratio divides by $R_s(q^s)$. Availability is the BCMP product form of each network on its own, a disclosed modeling choice (the paper invokes BCMP without writing the law). The paper writes $C>1$; the statement allows any number $C\ge1$ of networks ($C=1$ is the static half of Theorem 1). $N+K-1$ is computed in the reals. Within each network the accepted demand is strongly connected as a transitive closure, so every location has positive accepted demand $\lambda_i>0$; a location with no accepted demand (where the paper's (9) and $\alpha_i=r_i/\lambda_i$ are undefined) is not a network of this statement. Optimality of $q^s$ and $\Delta\ge K$ are the paper's hypotheses; of optimality the proof needs only that every network has nonnegative fluid reward.
-- source:
--   Benjaafar & Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN abstract 3998297 (version of 2023-01-10), p. 18, Theorem 4 (static half; the first inequality is Proposition 1, p. 6, not formalized)

import Mathlib
import Definitions.Def_VehicleSharePricing_MultiNet_Model

namespace VehicleSharePricing.MultiNet

/-- Theorem 4, p. 18, static half: when the optimal static policy `q^s` of Problem (2) splits the
network into connected networks and `K*` is an optimal allocation of the `K` vehicles to them
(Problem (8)), `R(q^s, K*) / R_s(q^s) ≥ K / (N + K - 1 + Λ/μ)`.
The page's first inequality `R(q^s,K*)/R(q*) ≥ R(q^s,K*)/R_s(q^s)` (Proposition 1) is not part of
this statement. -/
theorem theorem_4 {L ι : Type*} [Fintype L] [DecidableEq L] [Nonempty L] [Fintype ι] [DecidableEq ι]
    (Λ μ : L → L → ℝ) (I : L → L → ℝ → ℝ) (Δ : ℝ) (K : ℕ) (q : L → L → ℝ) (r : L → ℝ)
    (comp : L → ι) (h : SplitStaticSetting Λ μ I Δ K q r comp)
    (hRs : 0 < rewardS Λ I q) (Kstar : ι → ℕ)
    (hKstar : IsOptimalAllocation Λ μ q I r comp K Kstar) :
    (K : ℝ) / ((Fintype.card L : ℝ) + (K : ℝ) - 1 + demandOverRate Λ μ) ≤
      reward Λ μ q I r comp Kstar / rewardS Λ I q := by sorry

end VehicleSharePricing.MultiNet
