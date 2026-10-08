-- Prove2me | Theorems.Thm_SubstitutePricing_Mixed_eq_29
-- name    : SubstitutePricing.Mixed.eq_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:17:55.238133+00:00
-- url     : https://prove2.me/theorems/26affb69-b576-405d-9e84-5519d632947a
-- title:
--   (29) — the mixed-pricing objective equals ξ^m_t(x, r) + π_{t−1}(x)
-- statement:
--   In the mixed pricing model (dynamic-pricing variates $\mathfrak n_1$, fixed prices $r^j$ on $\mathfrak n_2$), let $V$ be any function of the inventory (it stands for $\pi_{t-1}$), $x$ an inventory vector and $r$ a vector of dynamic prices. Then the one-period objective of the optimality equation (3) equals
--
--   $$
--   \sum_{i \in S_1(x)} \lambda P^i(r)\big[r^i - (V(x) - V(x - e^i))\big] + \sum_{j \in S_2(x)} \lambda P^j(r)\big[r^j - (V(x) - V(x - e^j))\big] + V(x),
--   $$
--
--   where $S_1(x)$ and $S_2(x)$ are the in-stock dynamic-pricing and fixed-pricing variates. With $V = \pi_{t-1}$ the bracket is the paper's $\xi^m_t(x, r)$, so the optimality equation becomes (29): $\pi_t(x) = \max_{r} \xi^m_t(x, r) + \pi_{t-1}(x)$.
--
--   The identity uses only $\sum_{i \in S(x)} P^i + P^0 = 1$; it separates the immediate margin from the continuation value.
-- source:
--   Dong, Kouvelis, Tian, Dynamic Pricing and Inventory Control of Substitute Products, Manufacturing & Service Operations Management 11(2) (2009), p. 337, App. A, proof of Proposition 2, (29)

import Definitions.Def_SubstitutePricing_Mixed_Model

namespace SubstitutePricing.Mixed
/-- (29): the mixed-pricing objective equals the price objective plus the continuation value. -/
theorem eq_29 (M : Model) (hM : M.Assumptions) (V : (Fin M.n → ℕ) → ℝ)
    (x : Fin M.n → ℕ) (r : Fin M.n → ℝ) :
    M.objM V x r = M.xiM V x r + V x := by sorry
end SubstitutePricing.Mixed
