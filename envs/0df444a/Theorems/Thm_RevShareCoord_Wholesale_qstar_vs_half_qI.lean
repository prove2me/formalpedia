-- Prove2me | Theorems.Thm_RevShareCoord_Wholesale_qstar_vs_half_qI
-- name    : RevShareCoord.Wholesale.qstar_vs_half_qI
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T02:06:52.390675+00:00
-- url     : https://prove2.me/theorems/27c0ca58-60fa-465d-a49a-e0fe72565252
-- title:
--   Sec. 4.1.1, pp. 17–18 — q* ≥ q_I/2 for concave and q* ≤ q_I/2 for convex marginal revenue
-- statement:
--   In the single-retailer model of Sec. 1 with the assumptions of Sec. 4.1.1 (see the model definition), let $q^* \ge 0$ maximize the supplier's profit $\pi_s(q) = q(R'(q)-c)$ over $q \ge 0$, and let $q_I \ge 0$ maximize the supply chain profit $\Pi(q) = R(q) - qc$ over $q \ge 0$. Then:
--
--   1. if $R'$ is convex on $[0,\infty)$, then $2q^* \le q_I$;
--   2. if $R'$ is concave on $[0,\infty)$, then $q_I \le 2q^*$;
--   3. if $R'$ is strictly convex on $[0,\infty)$, then $2q^* < q_I$;
--   4. if $R'$ is strictly concave on $[0,\infty)$, then $q_I < 2q^*$.
--
--   In particular, for a linear marginal revenue curve,
--
--   $$
--   2q^* = q_I .
--   $$
--
--   The decentralized channel under the supplier's best wholesale price stocks less than half the integrated quantity when marginal revenue is strictly convex, and more than half when it is strictly concave.
--
--   **Formalization Note** The page states the strict forms "$q^* > q_I/2$ ($< q_I/2$) when marginal revenue is concave (convex)" together with $2q^* = q_I$ for linear marginal revenue; mere convexity includes the linear case, so the strict forms are stated under strict convexity or concavity.
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), p. 17 (PDF 18), Section 4.1.1, 'this also implies that q* > q_I/2 (< q_I/2)'; p. 18 (PDF 19), 'for a linear marginal revenue curve 2q* = q_I'

import Mathlib
import Definitions.Def_RevShareCoord_Wholesale_Model

namespace RevShareCoord.Wholesale

/-- Sec. 4.1.1 (pp. 17–18): the supplier's optimal quantity to induce `q*` satisfies
`q* ≥ q_I / 2` if marginal revenue `R'` is concave on `[0, ∞)` and `q* ≤ q_I / 2` if it is
convex, strictly under strict concavity or convexity (so `2q* = q_I` when `R'` is linear). -/
theorem qstar_vs_half_qI (M : Model) (qs qI : ℝ) (hqs0 : 0 ≤ qs)
    (hqs : IsMaxOn (supplierProfit M.R' M.c) (Set.Ici 0) qs)
    (hqI0 : 0 ≤ qI) (hqI : IsMaxOn (chainProfit M.R M.c) (Set.Ici 0) qI) :
    (ConvexOn ℝ (Set.Ici 0) M.R' → 2 * qs ≤ qI) ∧
      (ConcaveOn ℝ (Set.Ici 0) M.R' → qI ≤ 2 * qs) ∧
      (StrictConvexOn ℝ (Set.Ici 0) M.R' → 2 * qs < qI) ∧
      (StrictConcaveOn ℝ (Set.Ici 0) M.R' → qI < 2 * qs) := by sorry

end RevShareCoord.Wholesale
