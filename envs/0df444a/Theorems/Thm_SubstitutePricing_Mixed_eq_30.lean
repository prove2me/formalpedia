-- Prove2me | Theorems.Thm_SubstitutePricing_Mixed_eq_30
-- name    : SubstitutePricing.Mixed.eq_30
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:17:48.312015+00:00
-- url     : https://prove2.me/theorems/33039701-809f-4506-805b-efe138336d48
-- title:
--   (30) — P^0 and the fixed-price probabilities P^j in terms of the dynamic choice probabilities
-- statement:
--   In the mixed pricing model, let $\theta_j = e^{(a_j - r^j - u_0)/\mu}$ for a fixed-price variate $j$ and $\Theta = \sum_{j \in S_2(x)} \theta_j$. For every inventory $x$ and every vector $r$ of dynamic prices,
--
--   $$
--   P^0 = \frac{1}{1 + \Theta}\Big(1 - \sum_{i \in S_1(x)} P^i\Big), \qquad P^j = \frac{\theta_j}{1 + \Theta}\Big(1 - \sum_{i \in S_1(x)} P^i\Big) \quad (j \in S_2(x)),
--   $$
--
--   where all probabilities are those of (1)–(2) at the full price vector (dynamic prices $r$ on $\mathfrak n_1$, fixed prices on $\mathfrak n_2$).
--
--   Because the fixed prices do not move, the no-purchase and fixed-price probabilities are determined by the dynamic ones; this is what lets the optimization be carried out over the dynamic choice probabilities alone.
-- source:
--   Dong, Kouvelis, Tian, Dynamic Pricing and Inventory Control of Substitute Products, Manufacturing & Service Operations Management 11(2) (2009), p. 337, App. A, proof of Proposition 2, (30)

import Definitions.Def_SubstitutePricing_Mixed_Model

namespace SubstitutePricing.Mixed
/-- (30): the no-purchase and fixed-price choice probabilities in terms of the dynamic ones. -/
theorem eq_30 (M : Model) (hM : M.Assumptions) (x : Fin M.n → ℕ) (r : Fin M.n → ℝ) :
    M.P0 x (M.mix r) = (1 - ∑ i ∈ M.S1 x, M.P x (M.mix r) i) / (1 + M.Θ x) ∧
    ∀ j ∈ M.S2 x, M.P x (M.mix r) j =
      M.θ j * (1 - ∑ i ∈ M.S1 x, M.P x (M.mix r) i) / (1 + M.Θ x) := by sorry
end SubstitutePricing.Mixed
