-- Prove2me | Theorems.Thm_RevShareCoord_Single_profit_split
-- name    : RevShareCoord.Single.profit_split
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T20:41:59.11799+00:00
-- url     : https://prove2.me/theorems/44369e5e-ce48-4192-8ac4-edf45457e1fc
-- title:
--   Sec. 2.2, p. 6 — under {φ, φc}, π_r(q) = φΠ(q) and π_s(q) = (1 − φ)Π(q) at every quantity q
-- statement:
--   In the single-retailer model, let the supplier offer the revenue-sharing contract $\{\phi, w(\phi)\}$ with wholesale price $w(\phi) = \phi c$. Then for every order quantity $q$ the retailer's and the supplier's profits are fixed shares of the supply chain profit $\Pi(q) = R(q) - qc$:
--
--   $$
--   \pi_r(q) = \phi\,\Pi(q), \qquad \pi_s(q, w(\phi), \phi) = (1-\phi)\,\Pi(q).
--   $$
--
--   Hence $\phi$ is not only the fraction of revenue the retailer keeps but also the fraction of supply chain profit he receives.
--
--   **Formalization Note.** The paper displays these identities at $q = q_I$; they hold at every $q$ and for every real $\phi$, which is how they are stated. The paper's middle term "$\phi R(q_I) - q_I c$" is a slip for $\phi R(q_I) - q_I\phi c$ (as printed it equals $\phi\Pi(q_I)$ only when $\phi = 1$); the outer equality $\pi_r(q_I) = \phi\Pi(q_I)$ is the one stated. $\pi_s$ is the supplier's profit $(1-\phi)R(q) + qw - qc$ read off the sequence of events of Sec. 1.
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), p. 6 (PDF p. 7), Section 2.2, displays π_r(q_I) = φΠ(q_I) and π_s(q_I, w(φ), φ) = (1 − φ)Π(q_I)

import Mathlib
import Definitions.Def_RevShareCoord_Single_Model

namespace RevShareCoord.Single

/-- Sec. 2.2, p. 6: under the contract `{φ, φc}` the retailer earns the share `φ` and the
supplier the share `1 − φ` of the supply chain profit, at every order quantity `q`. -/
theorem profit_split (M : Model) (φ q : ℝ) :
    M.retailerProfit φ (φ * M.c) q = φ * M.Pi q ∧
      M.supplierProfit φ (φ * M.c) q = (1 - φ) * M.Pi q := by sorry

end RevShareCoord.Single
