-- Prove2me | Theorems.Thm_SubstitutePricing_Mixed_eq_32_34
-- name    : SubstitutePricing.Mixed.eq_32_34
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:18:11.335877+00:00
-- url     : https://prove2.me/theorems/15253ee1-16f6-4f89-ba96-3e0b223698ca
-- title:
--   (32)–(34) — at an optimum every in-stock dynamic price equals its marginal value plus the common margin m_t
-- statement:
--   In the mixed pricing model, fix an inventory $x$ and arbitrary real numbers $\delta_i$ (standing for $\Delta^i\pi_{t-1}(x)$), and consider the price objective
--
--   $$
--   \xi(r) = \sum_{i \in S_1(x)} \lambda P^i(r)\,[r^i - \delta_i] + \sum_{j \in S_2(x)} \lambda P^j(r)\,[r^j - \delta_j]
--   $$
--
--   as a function of the dynamic prices $r \in \mathbb R^{n_1}$ (the fixed prices $r^j$, $j \in \mathfrak n_2$, are data). If $r^*$ maximizes $\xi$ over all real dynamic prices, then, with
--
--   $$
--   m = \frac{\mu}{(1+\Theta)P^{0}(r^*)} + \frac{1}{1+\Theta}\sum_{j \in S_2(x)} \theta_j\,[r^j - \delta_j] \qquad (32),
--   $$
--
--   every in-stock dynamic price satisfies $r^{k*} = \delta_k + m$ for $k \in S_1(x)$ (34).
--
--   All dynamic variates thus carry the same margin over their marginal value; this is the form of the optimal prices in Proposition 2.
--
--   **Formalization Note** As in the paper's proof, the maximization is over the unconstrained price space (all real dynamic prices); the statement is about any maximizer and does not assert that one exists.
-- source:
--   Dong, Kouvelis, Tian, Dynamic Pricing and Inventory Control of Substitute Products, Manufacturing & Service Operations Management 11(2) (2009), p. 337, App. A, proof of Proposition 2, (32)–(34)

import Definitions.Def_SubstitutePricing_Mixed_Model

namespace SubstitutePricing.Mixed
/-- (32)–(34): at a maximizer of the price objective over all real dynamic prices, every
in-stock dynamic price equals its marginal value plus the common margin `m` of (32). -/
theorem eq_32_34 (M : Model) (hM : M.Assumptions) (x : Fin M.n → ℕ) (δ : Fin M.n → ℝ)
    (r : Fin M.n → ℝ) (hr : IsMaxOn (M.xiD x δ) Set.univ r) :
    ∀ k ∈ M.S1 x, r k = δ k +
      (M.μ / ((1 + M.Θ x) * M.P0 x (M.mix r)) +
        (∑ j ∈ M.S2 x, M.θ j * (M.rfix j - δ j)) / (1 + M.Θ x)) := by sorry
end SubstitutePricing.Mixed
