-- Prove2me | Theorems.Thm_SubstitutePricing_Mixed_proposition_2
-- name    : SubstitutePricing.Mixed.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:18:36.746673+00:00
-- url     : https://prove2.me/theorems/47d34ecc-3869-4836-b7db-d4a6cebf1b90
-- title:
--   Proposition 2 — optimal dynamic prices Δ^iπ_{t−1}(x) + m_t(x) when the other variates keep fixed prices
-- statement:
--   Consider the multinomial logit dynamic pricing model in which the variates of $\mathfrak n_2$ are sold at fixed prices $r^j$ and the variates of $\mathfrak n_1$ are priced dynamically. Let $t \ge 1$ be the number of remaining periods and $x$ the inventory, with in-stock sets $S_1(x)$ (dynamic) and $S_2(x)$ (fixed). Then:
--
--   1. The equation (15),
--   $$
--   \sum_{j \in S_2^+(x)} \Big(\Big(\frac{m_t(x) - v_j}{\mu} - 1\Big)\exp\Big(\frac{m_t(x) + u_j}{\mu}\Big)\Big) = \sum_{i \in S_1(x)} \exp\Big(\frac{a_i - \Delta^i\pi_{t-1}(x)}{\mu}\Big),
--   $$
--   where $S_2^+(x) = S_2(x) \cup \{0\}$, $v_0 = 0$, $v_j = r^j - \Delta^j\pi_{t-1}(x)$ and $u_j = a_j - r^j$ for $j \in S_2(x)$, has exactly one solution $m_t(x)$.
--   2. The dynamic prices $r^{i*}_t(x) = \Delta^i\pi_{t-1}(x) + m_t(x)$, $i \in S_1(x)$, are nonnegative, attain the maximum in the optimality equation, and the maximum equals $\pi_t(x)$.
--   3. The maximum expected revenue is
--   $$
--   \pi_t(x) = \lambda \sum_{s=1}^t \big[m_s(x) - \mu\big],
--   $$
--   where $m_s(x)$ is the solution of (15) for period $s$ at the same inventory $x$.
--
--   Here $\pi$ and $\Delta^i\pi_t(x) = \pi_t(x) - \pi_t(x - e^i)$ are those of the mixed-pricing problem, for $i$ in $S_1(x)$ and in $S_2(x)$. The fixed-price variates enter (15) in the same role as the outside option; when $\mathfrak n_2$ is empty, (15) reduces to the margin equation (10) of Theorem 1. Unlike in the full dynamic pricing model, $m_t P^{0*}_t = \mu$ does not hold here.
--
--   **Formalization Note** The paper's "for t = T, …, 0" is stated for $t \ge 1$; at $t = 0$ there is no decision and $\Delta\pi_{-1}$ is undefined. The case $S_1(x) = \emptyset$ is included: the right side of (15) is then $0$. The proof in the paper does not check that the prices $\Delta^i\pi_{t-1}(x) + m_t(x)$ lie in the price set $\mathbb R^{n_1}_+$ of (29) — $m_t > 0$ is not automatic here because nothing bounds $v_j$ from below — and the statement asserts it as printed. Fixed prices are assumed nonnegative.
-- source:
--   Dong, Kouvelis, Tian, Dynamic Pricing and Inventory Control of Substitute Products, Manufacturing & Service Operations Management 11(2) (2009), p. 329, Proposition 2 and (15); proof pp. 337–338

import Definitions.Def_SubstitutePricing_Mixed_Model

namespace SubstitutePricing.Mixed
/-- Proposition 2: optimal dynamic prices, the margin equation (15), and the maximum revenue
under mixed pricing. -/
theorem proposition_2 (M : Model) (hM : M.Assumptions) (t : ℕ) (ht : 1 ≤ t)
    (x : Fin M.n → ℕ) :
    (∃! m : ℝ, M.lhs15 t x m = M.rhs15 t x) ∧
    (∀ m : ℝ, M.lhs15 t x m = M.rhs15 t x →
      M.rstarM t x m ∈ M.feasibleM ∧
      IsMaxOn (M.objM (M.piM (t - 1)) x) M.feasibleM (M.rstarM t x m) ∧
      M.piM t x = M.objM (M.piM (t - 1)) x (M.rstarM t x m)) ∧
    (∀ ms : ℕ → ℝ,
      (∀ s ∈ Finset.Icc 1 t, M.lhs15 s x (ms s) = M.rhs15 s x) →
      M.piM t x = M.lam * ∑ s ∈ Finset.Icc 1 t, (ms s - M.μ)) := by sorry
end SubstitutePricing.Mixed
