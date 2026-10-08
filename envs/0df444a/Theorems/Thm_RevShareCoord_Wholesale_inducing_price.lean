-- Prove2me | Theorems.Thm_RevShareCoord_Wholesale_inducing_price
-- name    : RevShareCoord.Wholesale.inducing_price
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T02:06:24.033033+00:00
-- url     : https://prove2.me/theorems/6fc92129-7182-4f3b-acd5-c7c3f79fed27
-- title:
--   Sec. 4.1.1, Eq. (9) — the wholesale price w(q) = R′(q) makes q the retailer's unique optimal order
-- statement:
--   Consider the single-retailer model: revenue $R$ strictly concave and differentiable on $[0,\infty)$ with derivative $R'$, and unit cost $c > 0$. Under a wholesale-price contract with price $w$, the retailer orders a quantity $x \ge 0$ maximizing $R(x) - wx$.
--
--   For every $q \ge 0$, set $w(q) = R'(q)$. Then $q$ is the retailer's unique optimal order quantity at this price:
--
--   $$
--   R(q) - w(q)\,q \;\ge\; R(x) - w(q)\,x \quad\text{for all } x \ge 0,
--   $$
--
--   and every $x \ge 0$ attaining the maximum equals $q$.
--
--   This justifies parametrizing the supplier's choice of a wholesale price by the quantity it induces: the supplier who wants the retailer to order $q$ charges $w(q) = R'(q)$, and her profit becomes $\pi_s(q) = q(R'(q) - c)$.
--
--   **Formalization Note** Optimality is maximization over all $x \ge 0$, not the first-order condition. At $q = 0$ the statement says that the price $R'(0)$ induces the order $0$, the paper's corner case "otherwise the optimal order quantity is zero".
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), p. 16 (PDF 17), Section 4.1.1, Eq. (9) and the sentence 'From (9) it must be that w(q) = R'(q)'

import Mathlib
import Definitions.Def_RevShareCoord_Wholesale_Model

namespace RevShareCoord.Wholesale

/-- Sec. 4.1.1, Eq. (9) (p. 16): under the wholesale price `w(q) = R'(q)` the order `q ≥ 0`
is the retailer's unique optimal order quantity, i.e. the unique maximizer of
`x ↦ R(x) − w(q) x` over `x ≥ 0`. -/
theorem inducing_price (M : Model) (q : ℝ) (hq : 0 ≤ q) :
    IsMaxOn (fun x => M.R x - inducingPrice M.R' q * x) (Set.Ici 0) q ∧
      ∀ x : ℝ, 0 ≤ x →
        IsMaxOn (fun y => M.R y - inducingPrice M.R' q * y) (Set.Ici 0) x → x = q := by sorry

end RevShareCoord.Wholesale
