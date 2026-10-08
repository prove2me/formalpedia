-- Prove2me | Theorems.Thm_RevShareCoord_Wholesale_coordination_gain
-- name    : RevShareCoord.Wholesale.coordination_gain
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:07:03.659859+00:00
-- url     : https://prove2.me/theorems/6770ac56-4b48-49ef-afb8-881e9c5260ea
-- title:
--   Sec. 4.1.1, pp. 17–18 — coordination gains more (less) than half the supplier's profit for convex (concave) marginal revenue
-- statement:
--   In the single-retailer model of Sec. 1 with the assumptions of Sec. 4.1.1 (see the model definition), let $q^* \ge 0$ maximize the supplier's profit $\pi_s(q) = q(R'(q)-c)$ over $q \ge 0$, and let $q_I \ge 0$ maximize the supply chain profit $\Pi(q) = R(q) - qc$ over $q \ge 0$. The loss in supply chain profit from the supplier's optimal wholesale-price contract is
--
--   $$
--   \Pi(q_I) - \Pi(q^*) = \int_{q^*}^{q_I} \bigl(R'(z) - c\bigr)\,dz .
--   $$
--
--   Moreover:
--
--   1. if $R'$ is convex on $[0,\infty)$, then $\Pi(q_I) - \Pi(q^*) \ge \tfrac12 \pi_s(q^*)$;
--   2. if $R'$ is concave on $[0,\infty)$, then $\Pi(q_I) - \Pi(q^*) \le \tfrac12 \pi_s(q^*)$;
--   3. if $R'$ is strictly convex on $[0,\infty)$, then $\Pi(q_I) - \Pi(q^*) > \tfrac12 \pi_s(q^*)$;
--   4. if $R'$ is strictly concave on $[0,\infty)$, then $\Pi(q_I) - \Pi(q^*) < \tfrac12 \pi_s(q^*)$.
--
--   Hence coordinating the channel raises total profit by more than half of the supplier's profit when marginal revenue is convex, by less when it is concave, and by exactly half when it is linear.
--
--   **Formalization Note** The integral is the interval integral from $q^*$ to $q_I$. As in the companion statements, the strict comparisons ("more (less) than 50%") are stated under strict convexity or concavity, the weak ones under convexity or concavity; linear marginal revenue gives equality.
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), pp. 17-18 (PDF 18-19), Section 4.1.1, the displayed loss integral and the paragraph ending 'It increases by exactly 50% of the supplier's profit if marginal revenue is linear'

import Mathlib
import Definitions.Def_RevShareCoord_Wholesale_Model

namespace RevShareCoord.Wholesale

/-- Sec. 4.1.1 (pp. 17–18): the loss in supply chain profit from the supplier's optimal
wholesale-price contract is `Π(q_I) − Π(q*) = ∫_{q*}^{q_I} (R'(z) − c) dz`; it is at least
half of the supplier's profit `π_s(q*)` if marginal revenue `R'` is convex on `[0, ∞)` and
at most half if it is concave, strictly under strict convexity or concavity (so exactly half
when `R'` is linear). -/
theorem coordination_gain (M : Model) (qs qI : ℝ) (hqs0 : 0 ≤ qs)
    (hqs : IsMaxOn (supplierProfit M.R' M.c) (Set.Ici 0) qs)
    (hqI0 : 0 ≤ qI) (hqI : IsMaxOn (chainProfit M.R M.c) (Set.Ici 0) qI) :
    chainProfit M.R M.c qI - chainProfit M.R M.c qs =
        intervalIntegral (fun z => M.R' z - M.c) qs qI MeasureTheory.volume ∧
      (ConvexOn ℝ (Set.Ici 0) M.R' →
        supplierProfit M.R' M.c qs / 2 ≤ chainProfit M.R M.c qI - chainProfit M.R M.c qs) ∧
      (ConcaveOn ℝ (Set.Ici 0) M.R' →
        chainProfit M.R M.c qI - chainProfit M.R M.c qs ≤ supplierProfit M.R' M.c qs / 2) ∧
      (StrictConvexOn ℝ (Set.Ici 0) M.R' →
        supplierProfit M.R' M.c qs / 2 < chainProfit M.R M.c qI - chainProfit M.R M.c qs) ∧
      (StrictConcaveOn ℝ (Set.Ici 0) M.R' →
        chainProfit M.R M.c qI - chainProfit M.R M.c qs < supplierProfit M.R' M.c qs / 2) := by sorry

end RevShareCoord.Wholesale
