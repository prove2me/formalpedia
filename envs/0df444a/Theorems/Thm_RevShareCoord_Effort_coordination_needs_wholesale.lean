-- Prove2me | Theorems.Thm_RevShareCoord_Effort_coordination_needs_wholesale
-- name    : RevShareCoord.Effort.coordination_needs_wholesale
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T02:05:10.483611+00:00
-- url     : https://prove2.me/theorems/4639ec81-6405-45e0-8b9d-a7bb8bd67aba
-- title:
--   Sec. 4.2.1, p. 22 — only φ = 1 and w = c make (q_I, e_I) optimal for the retailer, leaving the supplier zero profit
-- statement:
--   In the model with retailer effort, let $(q_I, e_I)$ with $q_I > 0$, $e_I > 0$ maximize the integrated channel's profit $\Pi(q, e) = R(q, e) - g(e) - qc$ over $q, e \ge 0$, and suppose $\partial R(q_I, e_I)/\partial e > 0$. If a revenue-sharing contract $\{\phi, w\}$ with $\phi \in [0, 1]$ makes $(q_I, e_I)$ a maximizer of the retailer's profit $\pi_r(q, e) = \phi R(q, e) - g(e) - qw$ over $q, e \ge 0$, then
--
--   $$
--   \phi = 1, \qquad w = c, \qquad (1-\phi)R(q_I, e_I) + q_I(w - c) = 0 .
--   $$
--
--   So revenue sharing cannot coordinate the channel and leave the supplier a positive profit when retail effort affects demand: the only coordinating contract is the wholesale-price contract at marginal cost.
--
--   **Formalization Note.** As in the companion statement, the integrated solution is interior and $\partial R/\partial e > 0$ at it; both are added hypotheses. The supplier's profit is $(1-\phi)R + q(w - c)$, from the sequence of events of Sec. 1.
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), p. 22 (PDF p. 23), Section 4.2.1, 'In other words, the retailer chooses the optimal effort only if φ = 1. In that case the channel is coordinated only if the supplier sells at marginal cost, leaving her with no profit.'; p. 21 (PDF p. 22)

import Mathlib
import Definitions.Def_RevShareCoord_Effort_Model

namespace RevShareCoord.Effort

/-- Sec. 4.2.1, p. 22: if a revenue-sharing contract `{φ, w}` with `φ ∈ [0, 1]` makes the
integrated solution `(q_I, e_I)` optimal for the retailer, then `φ = 1`, `w = c`, and the
supplier earns zero profit. -/
theorem coordination_needs_wholesale (M : Model) (qI eI : ℝ) (hqI : 0 < qI) (heI : 0 < eI)
    (hopt : IsMaxOn (fun x : ℝ × ℝ => M.Pi x.1 x.2) (Set.Ici 0 ×ˢ Set.Ici 0) (qI, eI))
    (hRe : 0 < M.Re qI eI)
    (φ w : ℝ) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1)
    (hret : IsMaxOn (fun x : ℝ × ℝ => M.retailerProfit φ w x.1 x.2)
      (Set.Ici 0 ×ˢ Set.Ici 0) (qI, eI)) :
    φ = 1 ∧ w = M.c ∧ M.supplierProfit φ w qI eI = 0 := by sorry

end RevShareCoord.Effort
