-- Prove2me | Theorems.Thm_PersonalizedAssortment_IB_inventory_balancing_competitive_ratio
-- name    : PersonalizedAssortment.IB.inventory_balancing_competitive_ratio
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T01:57:54.472125+00:00
-- url     : https://prove2.me/theorems/7e292883-7381-42ea-bfcc-ba97bf5eca0d
-- title:
--   Theorem 1: inventory balancing with a concave penalty $\Psi$ is $\alpha_{c_{\min}}(\Psi)$-competitive
-- statement:
--   A firm sells $n\ge1$ products with revenues $r_i>0$ and initial inventories $c_i\in\{1,2,\dots\}$, with no replenishment. Let $c_{\min}=\min_i c_i$. Let $\mathcal S$ be a family of feasible assortments with $\emptyset\in\mathcal S$, which means the firm may offer nothing. Each customer type $z$ has a general choice model $\varphi^z$, and the family satisfies Assumption 1 (substitutability). Let $\Psi:[0,1]\to[0,1]$ be a penalty function: increasing, with $\Psi(0)=0$ and $\Psi(1)=1$. Suppose moreover that $\Psi$ is concave and twice differentiable on $[0,1]$.
--
--   Consider any horizon $T$ and any sequence of customer types $z_1,\dots,z_T$, possibly chosen by an adversary. In each period $t$, the inventory-balancing algorithm offers an assortment $S^t\in\mathcal S$ that maximizes $\sum_{i\in S}\Psi(I_i^{t-1}/c_i)\,r_i\,\varphi_i^{z_t}(S)$, breaking ties by the fewest products. Let $\mathrm{Rev}$ be its expected revenue. Then for every feasible solution $y$ of the benchmark linear program $\mathrm{Primal}(\{z_t\}_{t=1}^T)$,
--   $$\mathrm{Rev}\;\ge\;\alpha_{c_{\min}}(\Psi)\cdot\sum_{t=1}^T\sum_{S\in\mathcal S}\sum_{i=1}^n r_i\,\varphi_i^{z_t}(S)\,y^t(S),$$
--   where
--   $$\alpha_{c_{\min}}(\Psi)=\min_{x\in[0,\,1-1/c_{\min}]}\frac{1-x}{\dfrac1{c_{\min}}+1-\Psi(x)+\displaystyle\int_{x+1/c_{\min}}^{1}\Psi(y)\,dy}.$$
--   Equivalently, the competitive ratio of the algorithm against $\mathrm{Primal}(\{z_t\}_{t=1}^T)$ is at least $\alpha_{c_{\min}}(\Psi)$. The bound depends only on $c_{\min}$ and $\Psi$, not on $T$ or on the arrival sequence.
--
--   This is the main theorem of the paper. With $\Psi(x)=x$ the guarantee is $1/2$. With the exponential penalty it approaches $1-1/e$ as $c_{\min}\to\infty$, which is optimal.
--
--   **Formalization Note** Definition 2 defines the competitive ratio as $\inf_T\inf_{\{z_t\}}\mathrm{Rev}/\mathrm{Primal}$. That ratio form is not used. In Lean, $0/0=0$ would make it false when the LP value is $0$ (for instance when no product is ever bought), and a real infimum over an unbounded family is a junk value. The statement is instead the equivalent multiplied form for every horizon, every arrival sequence and every feasible $y$; since $\alpha_{c_{\min}}(\Psi)\ge0$, this is the same as comparing with the LP optimum. The case $T=0$ is allowed, and both sides are then $0$. The theorem holds for every selection rule meeting the maximization and tie-breaking specification. Twice differentiability is encoded as differentiability of $\Psi$ and of its derivative within $[0,1]$.
-- source:
--   Golrezaei, Nazerzadeh, Rusmevichientong, Real-Time Optimization of Personalized Assortments, Management Sci. 60(6), 2014, https://doi.org/10.1287/mnsc.2014.1939, p. 1538, Theorem 1 (proof in Section A.3, pp. 1548-1549)

import Mathlib
import Definitions.Def_PersonalizedAssortment_IB_ChoiceModel
import Definitions.Def_PersonalizedAssortment_IB_PenaltyFunction
import Definitions.Def_PersonalizedAssortment_IB_PrimalLP
import Definitions.Def_PersonalizedAssortment_IB_InventoryBalancing

namespace PersonalizedAssortment.IB

/-- Theorem 1 (Competitive Ratio), p. 1538. Let `c_min = min_i c_i` and let `Ψ` be an increasing,
concave, twice-differentiable penalty function. For every arrival sequence `z_1, …, z_T` of any
length, every inventory-balancing selection rule and every feasible solution `y` of
`Primal({z_t})`, the expected revenue of inventory balancing is at least `α_{c_min}(Ψ)` times the
objective of `y`. Standing assumptions: `r_i > 0`, `c_i ∈ ℤ_+` positive, `∅ ∈ 𝒮` (§2),
Assumption 1 (p. 1537), `Ψ : [0,1] → [0,1]` with `Ψ(0) = 0`, `Ψ(1) = 1` (§3). -/
theorem inventory_balancing_competitive_ratio {n : ℕ} (hn : 0 < n) {Z : Type*}
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) (c : Fin n → ℕ) (hc : ∀ i, 0 < c i)
    (𝒮 : Finset (Finset (Fin n))) (h𝒮 : ∅ ∈ 𝒮) (φ : Z → ChoiceModel n)
    (hsub : Substitutable 𝒮 φ) (Ψ : ℝ → ℝ) (hΨ : IsPenaltyFunction Ψ)
    (hconc : ConcaveOn ℝ (Set.Icc 0 1) Ψ) (hdiff : DifferentiableOn ℝ Ψ (Set.Icc 0 1))
    (hdiff2 : DifferentiableOn ℝ (derivWithin Ψ (Set.Icc 0 1)) (Set.Icc 0 1))
    {T : ℕ} (z : Fin T → Z) (sel : Fin T → (Fin n → ℕ) → Finset (Fin n))
    (hsel : IsIBRule Ψ r c 𝒮 φ z sel)
    (y : Fin T → Finset (Fin n) → ℝ) (hy : PrimalFeasible c 𝒮 φ z y) :
    alphaC Ψ (cMin c hn) * primalObj r 𝒮 φ z y ≤ ibRevenue r c φ z sel := by sorry

end PersonalizedAssortment.IB
