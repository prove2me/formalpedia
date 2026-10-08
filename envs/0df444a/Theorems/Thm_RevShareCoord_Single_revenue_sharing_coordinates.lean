-- Prove2me | Theorems.Thm_RevShareCoord_Single_revenue_sharing_coordinates
-- name    : RevShareCoord.Single.revenue_sharing_coordinates
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T20:41:59.665035+00:00
-- url     : https://prove2.me/theorems/78c96455-014b-44b0-9c85-4d96d49452d6
-- title:
--   Sec. 2.2, p. 6 — revenue sharing {φ, φc} coordinates the channel: q_I is the retailer's unique optimum, φc ≤ c, and the profits split as φΠ(q_I), (1 − φ)Π(q_I)
-- statement:
--   Consider the single-retailer model: the retailer's expected revenue $R(q)$ is strictly concave and differentiable for $q \ge 0$, the supplier's unit cost is $c > 0$, $R'(0) > c$ and $R'(\infty) < c$. Let $q_I$ be the integrated channel's optimal order quantity, i.e. a maximizer of $\Pi(q) = R(q) - qc$ over $q \ge 0$. Let $\phi \in (0, 1]$ and let the supplier offer the revenue-sharing contract $\{\phi, w(\phi)\}$ with
--
--   $$
--   w(\phi) = \phi c .
--   $$
--
--   Then:
--
--   1. $q_I$ is the retailer's unique optimal order quantity, i.e. the unique maximizer of $\pi_r(q) = \phi R(q) - q\,w(\phi)$ over $q \ge 0$;
--   2. the supplier sells at or below cost: $w(\phi) \le c$;
--   3. the retailer earns the share $\phi$ of the maximal supply chain profit: $\pi_r(q_I) = \phi\,\Pi(q_I)$;
--   4. the supplier earns the rest: $\pi_s(q_I, w(\phi), \phi) = (1-\phi)\,\Pi(q_I)$.
--
--   Thus with revenue sharing the supplier can maximize total supply chain profit and take any share of it for herself; this is the sense in which revenue sharing coordinates the channel and arbitrarily divides its profit.
--
--   **Formalization Note.** $\phi = 0$ is excluded: then $\pi_r \equiv 0$ and every quantity is optimal for the retailer, so $q_I$ is not the unique optimum (the paper's argument, $\pi_r = \phi\Pi$, needs $\phi > 0$). The paper's middle term "$\phi R(q_I) - q_I c$" is a slip for $\phi R(q_I) - q_I\phi c$; the outer equality is stated. The supplier's profit $\pi_s(q) = (1-\phi)R(q) + qw - qc$ is read off Sec. 1's sequence of events. $R$ is differentiable on $[0,\infty)$ with a one-sided derivative at $0$, and $R'(\infty) < c$ is encoded as "$R'(Q) < c$ for some $Q \ge 0$".
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), p. 6 (PDF p. 7), Section 2.2, the passage from 'The retailer's optimal order quantity equals q_I when the wholesale price is w(φ) = φc' to 'take any share of that profit for herself'

import Mathlib
import Definitions.Def_RevShareCoord_Single_Model

namespace RevShareCoord.Single

/-- Sec. 2.2, p. 6 (goal): let `q_I` be the integrated channel's optimal order quantity and let
`φ ∈ (0, 1]`. Under the revenue-sharing contract `{φ, w(φ)}` with `w(φ) = φc`:
(1) `q_I` is the retailer's unique optimal order quantity; (2) `w(φ) ≤ c`;
(3) `π_r(q_I) = φΠ(q_I)`; (4) `π_s(q_I, w(φ), φ) = (1 − φ)Π(q_I)`. -/
theorem revenue_sharing_coordinates (M : Model) (φ : ℝ) (hφ0 : 0 < φ) (hφ1 : φ ≤ 1)
    (qI : ℝ) (hqI0 : 0 ≤ qI) (hqI : IsMaxOn M.Pi (Set.Ici 0) qI) :
    (IsMaxOn (M.retailerProfit φ (φ * M.c)) (Set.Ici 0) qI ∧
      ∀ q : ℝ, 0 ≤ q → IsMaxOn (M.retailerProfit φ (φ * M.c)) (Set.Ici 0) q → q = qI) ∧
    φ * M.c ≤ M.c ∧
    M.retailerProfit φ (φ * M.c) qI = φ * M.Pi qI ∧
    M.supplierProfit φ (φ * M.c) qI = (1 - φ) * M.Pi qI := by sorry

end RevShareCoord.Single
