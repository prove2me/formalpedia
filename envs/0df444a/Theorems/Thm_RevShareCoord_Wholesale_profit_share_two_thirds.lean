-- Prove2me | Theorems.Thm_RevShareCoord_Wholesale_profit_share_two_thirds
-- name    : RevShareCoord.Wholesale.profit_share_two_thirds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:06:44.530461+00:00
-- url     : https://prove2.me/theorems/94069801-7b42-4862-a186-fff81169ffc6
-- title:
--   Sec. 4.1.1, p. 17 — the supplier's profit share is below 2/3 for convex and above 2/3 for concave marginal revenue
-- statement:
--   In the single-retailer model of Sec. 1 with the assumptions of Sec. 4.1.1 (see the model definition), let $q^* \ge 0$ maximize the supplier's profit $\pi_s(q) = q(R'(q)-c)$ over $q \ge 0$. The supplier's profit share is
--
--   $$
--   \frac{\pi_s(q^*)}{\Pi(q^*)}, \qquad \Pi(q^*) = R(q^*) - q^* c = \pi_s(q^*) + \pi_r(q^*).
--   $$
--
--   Then:
--
--   1. if the marginal revenue $R'$ is convex on $[0,\infty)$, the share is at most $2/3$;
--   2. if $R'$ is concave on $[0,\infty)$, the share is at least $2/3$;
--   3. if $R'$ is strictly convex on $[0,\infty)$, the share is strictly less than $2/3$;
--   4. if $R'$ is strictly concave on $[0,\infty)$, the share is strictly more than $2/3$.
--
--   In particular the share is exactly $2/3$ when marginal revenue is linear. The comparison says how much of the decentralized channel's profit the supplier keeps under her best wholesale-price contract, depending only on the curvature of marginal revenue.
--
--   **Formalization Note** The paper says "less (more) than 2/3rds if the marginal revenue is convex (concave)". Under mere convexity the linear case gives exactly $2/3$, so the strict inequalities are stated under strict convexity or concavity and the weak ones under convexity or concavity. The statement uses $R(0) = 0$ from the model.
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), p. 17 (PDF 18), Section 4.1.1, profit-share definition and the paragraph on the triangle a_2 and the rectangle a_3

import Mathlib
import Definitions.Def_RevShareCoord_Wholesale_Model

namespace RevShareCoord.Wholesale

/-- Sec. 4.1.1 (p. 17): the supplier's profit share `π_s(q*) / Π(q*)` at her optimal
quantity to induce `q*` is at most `2/3` if marginal revenue `R'` is convex on `[0, ∞)`
and at least `2/3` if it is concave, strictly so under strict convexity or concavity. -/
theorem profit_share_two_thirds (M : Model) (qs : ℝ) (hqs0 : 0 ≤ qs)
    (hqs : IsMaxOn (supplierProfit M.R' M.c) (Set.Ici 0) qs) :
    (ConvexOn ℝ (Set.Ici 0) M.R' → profitShare M.R M.R' M.c qs ≤ 2 / 3) ∧
      (ConcaveOn ℝ (Set.Ici 0) M.R' → 2 / 3 ≤ profitShare M.R M.R' M.c qs) ∧
      (StrictConvexOn ℝ (Set.Ici 0) M.R' → profitShare M.R M.R' M.c qs < 2 / 3) ∧
      (StrictConcaveOn ℝ (Set.Ici 0) M.R' → 2 / 3 < profitShare M.R M.R' M.c qs) := by sorry

end RevShareCoord.Wholesale
