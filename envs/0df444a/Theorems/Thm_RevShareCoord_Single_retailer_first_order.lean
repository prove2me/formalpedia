-- Prove2me | Theorems.Thm_RevShareCoord_Single_retailer_first_order
-- name    : RevShareCoord.Single.retailer_first_order
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T20:41:45.227987+00:00
-- url     : https://prove2.me/theorems/34a831a7-3bd5-4dcf-9d99-b31d3a2b9f94
-- title:
--   Sec. 2.2, p. 6 — with R′(0) > w/φ, the retailer's optimal order q̂ is positive and solves φR′(q̂) = w
-- statement:
--   In the single-retailer model, let the supplier offer the revenue-sharing contract $\{\phi, w\}$ with $\phi \in (0, 1]$ and $w \ge 0$, so that the retailer's profit is $\pi_r(q) = \phi R(q) - qw$. Assume
--
--   $$
--   R'(0) > \frac{w}{\phi}.
--   $$
--
--   Then an order quantity $\hat q \ge 0$ maximizes $\pi_r$ over $[0,\infty)$ if and only if $\hat q > 0$ and
--
--   $$
--   \phi R'(\hat q) = w ,
--   $$
--
--   and the retailer has at most one optimal order quantity.
--
--   This is the retailer's best response to a revenue-sharing contract; comparing it with Eq. (1) shows which wholesale price makes the retailer choose $q_I$.
--
--   **Formalization Note.** The paper states only the necessary direction ("the retailer's optimal order quantity, $\hat q$, must satisfy $\phi R'(\hat q) = w$"); the statement adds the converse (a positive solution of the first-order condition is optimal) and uniqueness, both of which the paper uses in the next sentence. It does not assert that an optimum exists: under the model's assumptions it may not (for instance when $w = 0$ and $R$ is increasing).
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), p. 6 (PDF p. 7), Section 2.2, displays π_r(q) = φR(q) − qw and φR′(q̂) = w

import Mathlib
import Definitions.Def_RevShareCoord_Single_Model

namespace RevShareCoord.Single

/-- Sec. 2.2, p. 6: under a revenue-sharing contract `{φ, w}` with `φ ∈ (0, 1]`, `w ≥ 0` and
`R'(0) > w/φ`, an order quantity `q̂ ≥ 0` is optimal for the retailer exactly when `q̂ > 0` and
`φR'(q̂) = w`; and the retailer has at most one optimal order quantity. -/
theorem retailer_first_order (M : Model) (φ w : ℝ) (hφ0 : 0 < φ) (hφ1 : φ ≤ 1) (hw : 0 ≤ w)
    (hR0 : w / φ < M.R' 0) :
    (∀ qhat : ℝ, 0 ≤ qhat →
      (IsMaxOn (M.retailerProfit φ w) (Set.Ici 0) qhat ↔ 0 < qhat ∧ φ * M.R' qhat = w)) ∧
    (∀ q₁ q₂ : ℝ, 0 ≤ q₁ → 0 ≤ q₂ →
      IsMaxOn (M.retailerProfit φ w) (Set.Ici 0) q₁ →
      IsMaxOn (M.retailerProfit φ w) (Set.Ici 0) q₂ → q₁ = q₂) := by sorry

end RevShareCoord.Single
