-- Prove2me | Theorems.Thm_RevShareCoord_Competing_wI_above_cost
-- name    : RevShareCoord.Competing.wI_above_cost
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:17:32.083468+00:00
-- url     : https://prove2.me/theorems/0494ff89-9d5f-4600-b670-bad0af22999f
-- title:
--   Sec. 3.2 — with substitutes, the coordinating wholesale price w_i^I is at least the marginal cost c
-- statement:
--   In the competing-retailers model, let $\bar q^I$ be a profile and suppose the locations are substitutes at $\bar q^I$ in the sense that more stock at location $i$ does not raise revenue at any other location:
--   $$R_j^i(\bar q^I) = \frac{\partial R_j}{\partial q_i}(\bar q^I) \le 0 \qquad \text{for all } j \ne i.$$
--   Then the coordinating wholesale price $w_i^I = c - \sum_{j\neq i} R_j^i(\bar q^I)$ satisfies
--   $$w_i^I \ge c \qquad \text{for every } i,$$
--   and $w_i^I > c$ for every $i$ for which some $R_j^i(\bar q^I)$, $j \ne i$, is strictly negative.
--
--   Coordination with competing retailers thus requires linear prices above the marginal cost of production, which is what lets the supplier earn a positive profit while coordinating.
--
--   **Formalization Note** The paper writes "Because $R_j^i(\bar q) \le 0$, $w_i^I$ is greater than the marginal cost". The sign condition $R_j^i \le 0$ is not among the stated assumptions of Section 3.2 (which bound the cross-partial $\partial^2 R_i/\partial q_i\partial q_j$), so it is a hypothesis here. "Greater" is strict only when some cross-effect is strictly negative; the strict part carries that condition.
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), p. 13 (PDF p. 14), Section 3.2, last paragraph

import Mathlib
import Definitions.Def_RevShareCoord_Competing_Game
import Definitions.Def_RevShareCoord_Competing_Model

namespace RevShareCoord.Competing

open Finset

/-- **Sec. 3.2, `w_i^I` above marginal cost (p. 13).** Index convention:
`M.dR i j q = R_j^i(q̄) = ∂R_j/∂q_i`. If `R_j^i(q̄^I) ≤ 0` for all `j ≠ i` (raising the quantity at
one location does not raise revenue at another), then `w_i^I = c − Σ_{j≠i} R_j^i(q̄^I) ≥ c` for
every `i`, with strict inequality for every `i` such that `R_j^i(q̄^I) < 0` for some `j ≠ i`. -/
theorem wI_above_cost {n : ℕ} (M : Model n) (qI : Fin n → ℝ)
    (hsub : ∀ i j, j ≠ i → M.dR i j qI ≤ 0) :
    (∀ i, M.c ≤ M.wI qI i) ∧
      ∀ i, (∃ j, j ≠ i ∧ M.dR i j qI < 0) → M.c < M.wI qI i := by sorry

end RevShareCoord.Competing
