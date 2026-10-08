-- Prove2me | Theorems.Thm_RevShareCoord_Effort_effort_below_integrated
-- name    : RevShareCoord.Effort.effort_below_integrated
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T02:04:56.100439+00:00
-- url     : https://prove2.me/theorems/82af1bb2-8253-491b-8cc6-6803e74b935e
-- title:
--   Sec. 4.2.1, p. 22 — with w = φc and φ < 1, the retailer's optimal effort at q_I is below e_I
-- statement:
--   In the model with retailer effort, let $(q_I, e_I)$ with $q_I > 0$, $e_I > 0$ maximize the integrated channel's profit $\Pi(q, e) = R(q, e) - g(e) - qc$ over $q, e \ge 0$, and suppose $\partial R(q_I, e_I)/\partial e > 0$. Let $0 \le \phi < 1$ and let the supplier charge the wholesale price $w = \phi c$, the price under which $q_I$ satisfies the retailer's first-order condition in $q$ at effort $e_I$. Suppose the retailer's profit at $q_I$,
--
--   $$
--   \pi_r(q_I, e) = \phi R(q_I, e) - g(e) - q_I\phi c,
--   $$
--
--   is strictly concave in $e \ge 0$. Then every effort level $e \ge 0$ that maximizes $\pi_r(q_I, \cdot)$ over $e \ge 0$ satisfies $e < e_I$.
--
--   The statement is the first half of the section's negative result: a revenue-sharing contract that leaves the supplier a share of revenue weakens the retailer's incentive to exert effort.
--
--   **Formalization Note.** The page states the strict concavity of $\pi_r(q_I, \cdot)$ as a fact, but it does not follow from the model's assumptions ($R$ is only assumed concave in $q$), so it is a hypothesis. $\partial R/\partial e > 0$ at $(q_I, e_I)$ is added because "strictly increasing in $e$" only gives a nonnegative derivative, and with a zero derivative the page's strict inequality fails. The integrated solution is taken interior ($q_I, e_I > 0$), which is the reading under which the page's first-order conditions (11)–(12) hold.
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), p. 22 (PDF p. 23), Section 4.2.1, display of ∂π_r(q^I, e^I)/∂e < 0 and 'so the retailer's optimal effort is less than e^I if φ < 1'; Eqs. (11)–(12)

import Mathlib
import Definitions.Def_RevShareCoord_Effort_Model

namespace RevShareCoord.Effort

/-- Sec. 4.2.1, p. 22: under revenue sharing with the coordinating wholesale price `w = φc` and
`φ < 1`, the retailer's optimal effort at the integrated quantity `q_I` is below `e_I`. -/
theorem effort_below_integrated (M : Model) (qI eI : ℝ) (hqI : 0 < qI) (heI : 0 < eI)
    (hopt : IsMaxOn (fun x : ℝ × ℝ => M.Pi x.1 x.2) (Set.Ici 0 ×ˢ Set.Ici 0) (qI, eI))
    (hRe : 0 < M.Re qI eI)
    (φ : ℝ) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1)
    (hconc : StrictConcaveOn ℝ (Set.Ici 0) (fun e => φ * M.R qI e - M.g e)) :
    ∀ e : ℝ, 0 ≤ e →
      IsMaxOn (fun e' => M.retailerProfit φ (φ * M.c) qI e') (Set.Ici 0) e → e < eI := by sorry

end RevShareCoord.Effort
