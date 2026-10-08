-- Prove2me | Theorems.Thm_RevShareCoord_Wholesale_optimal_wholesale_price
-- name    : RevShareCoord.Wholesale.optimal_wholesale_price
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T02:06:35.999472+00:00
-- url     : https://prove2.me/theorems/ce083d6b-d7fe-4a04-86ee-fd99ed17624b
-- title:
--   Sec. 4.1.1, pp. 16–17 — the optimal wholesale price is w(q*) = c − q*R″(q*) and exceeds c
-- statement:
--   In the single-retailer model of Sec. 1 with the assumptions of Sec. 4.1.1 (see the model definition), let $q^* \ge 0$ maximize the supplier's profit $\pi_s(q) = q(R'(q) - c)$ over $q \ge 0$, and let $w(q^*) = R'(q^*)$ be the corresponding optimal wholesale price. Then
--
--   $$
--   w(q^*) = c - q^* R''(q^*),
--   $$
--
--   and
--
--   $$
--   w(q^*) > c .
--   $$
--
--   The supplier's optimal wholesale price is above marginal cost, in contrast with the coordinating revenue-sharing contract, whose wholesale price is below cost. The formula shows that the curvature of the marginal revenue curve governs the contract's efficiency and the supplier's profit share.
--
--   **Formalization Note** Both conclusions are stated in the model of Sec. 4.1.1 without a sign hypothesis on $R''$, as on the page. $q^*$ is characterized as a maximizer of $\pi_s$, not as a root of $\pi_s'$.
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), pp. 16-17 (PDF 17-18), Section 4.1.1, 'it follows ... that the optimal wholesale price w(q*) is greater than marginal cost' and 'the optimal wholesale price is w(q*) = c - q*R''(q*)'

import Mathlib
import Definitions.Def_RevShareCoord_Wholesale_Model

namespace RevShareCoord.Wholesale

/-- Sec. 4.1.1 (pp. 16–17): at the supplier's optimal quantity to induce `q*` (a maximizer
of `π_s` on `[0, ∞)`), the optimal wholesale price is `w(q*) = c − q* R''(q*)`, and it is
strictly above marginal cost `c`. -/
theorem optimal_wholesale_price (M : Model) (qs : ℝ) (hqs0 : 0 ≤ qs)
    (hqs : IsMaxOn (supplierProfit M.R' M.c) (Set.Ici 0) qs) :
    inducingPrice M.R' qs = M.c - qs * M.R'' qs ∧
      M.c < inducingPrice M.R' qs := by sorry

end RevShareCoord.Wholesale
