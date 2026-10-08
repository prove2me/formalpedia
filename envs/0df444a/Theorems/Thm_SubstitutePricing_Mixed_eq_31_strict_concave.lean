-- Prove2me | Theorems.Thm_SubstitutePricing_Mixed_eq_31_strict_concave
-- name    : SubstitutePricing.Mixed.eq_31_strict_concave
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:18:29.483986+00:00
-- url     : https://prove2.me/theorems/bdb4c733-f4b4-4e40-8044-c522fdc8af4f
-- title:
--   (31) — ξ^m_t is strictly jointly concave in the dynamic choice probabilities
-- statement:
--   In the mixed pricing model, fix an inventory $x$ and arbitrary real numbers $\delta_i$ (standing for the marginal values $\Delta^i\pi_{t-1}(x)$). For a vector $p = (p_i)_{i \in S_1(x)}$ of dynamic choice probabilities put $P^0(p) = \frac{1}{1+\Theta}\big(1 - \sum_{i \in S_1(x)} p_i\big)$ and $P^j = \theta_j P^0(p)$ for $j \in S_2(x)$, as in (30), and define
--
--   $$
--   \xi^m(p) = \sum_{i \in S_1(x)} \lambda p_i\big[a_i - u_0 - \mu \ln p_i + \mu \ln P^0(p) - \delta_i\big] + \sum_{j \in S_2(x)} \lambda \theta_j P^0(p)\,\big[r^j - \delta_j\big].
--   $$
--
--   Then $\xi^m$ is strictly concave on the open domain $\{p : p_i > 0 \ (i \in S_1(x)),\ \sum_{i \in S_1(x)} p_i < 1\}$.
--
--   Strict concavity is what makes the optimal probability vector, and hence the optimal dynamic prices, unique and characterized by the first-order conditions.
--
--   **Formalization Note** $p$ is a vector indexed by all variates; its coordinates outside $S_1(x)$ do not enter $\xi^m$ and are pinned to $0$ in the domain, without which strict concavity would fail for a trivial reason. $\lambda > 0$ and $\mu > 0$ are the model's standing assumptions.
-- source:
--   Dong, Kouvelis, Tian, Dynamic Pricing and Inventory Control of Substitute Products, Manufacturing & Service Operations Management 11(2) (2009), p. 337, App. A, proof of Proposition 2, (31) and the Hessian argument following it

import Definitions.Def_SubstitutePricing_Mixed_Model

namespace SubstitutePricing.Mixed
/-- (31): the objective in the dynamic choice probabilities is strictly concave. -/
theorem eq_31_strict_concave (M : Model) (hM : M.Assumptions) (x : Fin M.n → ℕ)
    (δ : Fin M.n → ℝ) :
    StrictConcaveOn ℝ (M.probDomain x) (M.xiProb x δ) := by sorry
end SubstitutePricing.Mixed
