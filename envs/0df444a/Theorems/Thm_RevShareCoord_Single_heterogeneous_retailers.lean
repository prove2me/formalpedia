-- Prove2me | Theorems.Thm_RevShareCoord_Single_heterogeneous_retailers
-- name    : RevShareCoord.Single.heterogeneous_retailers
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T20:41:52.838259+00:00
-- url     : https://prove2.me/theorems/4b1a1642-c548-48a1-99b2-a066edf1753e
-- title:
--   Sec. 2.2, p. 7 — one revenue-sharing contract coordinates heterogeneous retailers
-- statement:
--   Fix the unit cost $c > 0$ and a revenue share $\phi \in (0, 1]$. There is a single wholesale price $w \ge 0$ with the following property. For every retailer satisfying the single-retailer model with unit cost $c$ — whatever his revenue function $R$ — and every optimal quantity $q_I$ of his integrated channel (a maximizer of $\Pi(q) = R(q) - qc$ over $q \ge 0$), the order quantity $q_I$ is the retailer's unique optimal order under the contract $\{\phi, w\}$:
--
--   $$
--   q_I = \operatorname*{arg\,max}_{q \ge 0}\ \bigl(\phi R(q) - qw\bigr).
--   $$
--
--   In the paper's words, with revenue sharing the coordinating contract is independent of the marginal revenue curve, so the same contract coordinates retailers that face different demand. This is the contrast the paper draws with quantity-discount schedules, which must be tailored to each retailer's marginal revenue.
--
--   **Formalization Note.** The order of quantifiers carries the content: the wholesale price is chosen before, and independently of, the revenue function. (The price $w = \phi c$ works.)
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), p. 7 (PDF p. 8), Section 2.2, the sentence 'With revenue sharing the coordinating contract is independent of the marginal revenue curve, and so the same revenue sharing contract coordinates the actions of heterogenous retailers'

import Mathlib
import Definitions.Def_RevShareCoord_Single_Model

namespace RevShareCoord.Single

/-- Sec. 2.2, p. 7: the coordinating revenue-sharing contract is independent of the marginal
revenue curve. For a unit cost `c` and a revenue share `φ ∈ (0, 1]` there is one wholesale
price `w` such that every retailer, whatever his revenue function `R` (any model with unit
cost `c`), orders his own integrated-channel quantity `q_I` as his unique optimum. -/
theorem heterogeneous_retailers (c φ : ℝ) (hφ0 : 0 < φ) (hφ1 : φ ≤ 1) :
    ∃ w : ℝ, 0 ≤ w ∧ ∀ M : Model, M.c = c → ∀ qI : ℝ, 0 ≤ qI →
      IsMaxOn M.Pi (Set.Ici 0) qI →
      IsMaxOn (M.retailerProfit φ w) (Set.Ici 0) qI ∧
        ∀ q : ℝ, 0 ≤ q → IsMaxOn (M.retailerProfit φ w) (Set.Ici 0) q → q = qI := by sorry

end RevShareCoord.Single
