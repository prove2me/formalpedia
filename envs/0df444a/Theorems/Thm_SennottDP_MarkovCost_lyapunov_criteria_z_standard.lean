-- Prove2me | Theorems.Thm_SennottDP_MarkovCost_lyapunov_criteria_z_standard
-- name    : SennottDP.MarkovCost.lyapunov_criteria_z_standard
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T14:18:35.478986+00:00
-- url     : https://prove2.me/theorems/f2de6c41-467b-438f-88c7-93939fb576ab
-- title:
--   Remark C.2.7 — the Lyapunov criteria of C.1.6 and C.2.4 imply $z$ standard; so does irreducible positive recurrence with finite average cost
-- statement:
--   Let $\Gamma$ be a Markov chain on a countable state space $S$ with finite nonnegative costs $C(i)$.
--
--   1. If the hypotheses of Corollaries C.1.6 and C.2.4 hold for a state $z$, namely there are a finite nonnegative $y$ and $\epsilon > 0$ with $\sum_j P_{zj}\, y(j) < \infty$ and $\sum_j P_{ij}[y(j) - y(i)] \le -\epsilon$ for $i \ne z$, and a finite nonnegative $r$ and a finite set $H^* \ni z$ with $\sum_j P_{ij}\, r(j) < \infty$ for $i \in H^*$ and $\sum_j P_{ij}[r(j) - r(i)] \le -C(i)$ for $i \notin H^*$, then $\Gamma$ is $z$ standard.
--   2. If $\Gamma$ is irreducible and positive recurrent with finite average cost $J_S = \sum_{j} \pi_j C(j) < \infty$, then $\Gamma$ is $z$ standard for every state $z$.
--
--   Part 1 is the practical test for the $z$ standard property used throughout the book's queueing applications.
--
--   **Formalization Note** Drift conditions are written in the additive form $\sum_j P_{ij} y(j) + \epsilon \le y(i)$ and $\sum_j P_{ij} r(j) + C(i) \le r(i)$, equivalent for finite $y, r$. "Positive recurrent" for the irreducible chain means every state is positive recurrent, and its average cost is $J_R$ with $R = S$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), pp. 301–302, Remark C.2.7

import Mathlib
import Definitions.Def_SennottDP_MarkovCost_Chain
import Definitions.Def_SennottDP_MarkovCost_Costs

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.MarkovCost

/-- Sennott (1999), Remark C.2.7, pp. 301–302.
(i) If the hypotheses of Corollaries C.1.6 and C.2.4 hold (a Lyapunov function `y` with `ε > 0`,
`∑_j P_{zj} y(j) < ∞` and (C.10), and a finite nonnegative `r` with a finite set `H* ∋ z` satisfying
(C.16)), then `Γ` is `z` standard.
(ii) If `Γ` is irreducible and positive recurrent with finite average cost, then it is `z` standard
for any state `z`. -/
theorem lyapunov_criteria_z_standard {S : Type} [Countable S] (M : MC S) (C : S → ℝ≥0) :
    (∀ (z : S) (y : S → ℝ≥0) (ε : ℝ≥0), 0 < ε → ∑' j, M.P z j * (y j : ℝ≥0∞) < ⊤ →
      (∀ i, i ≠ z → ∑' j, M.P i j * (y j : ℝ≥0∞) + ε ≤ y i) →
      ∀ (r : S → ℝ≥0) (Hs : Finset S), z ∈ Hs →
      (∀ i ∈ Hs, ∑' j, M.P i j * (r j : ℝ≥0∞) < ⊤) →
      (∀ i ∉ Hs, ∑' j, M.P i j * (r j : ℝ≥0∞) + C i ≤ r i) →
      IsZStandard M C z) ∧
    (Irreducible M → (∀ i, PositiveRecurrent M i) → classAvgCost M C Set.univ < ⊤ →
      ∀ z, IsZStandard M C z) := by sorry

end SennottDP.MarkovCost
