-- Prove2me | Theorems.Thm_SpreadBetting_Inertial_theorem_3
-- name    : SpreadBetting.Inertial.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:32:31.45704+00:00
-- url     : https://prove2.me/theorems/61b75276-ed27-429a-855d-4212f84a0a6a
-- title:
--   Theorem 3, p. 17 — for r ∈ (0, r̄) with r̄ > 0 explicit, the informed bettor's profit is finite and the threshold strategy (4.4) is his best response
-- statement:
--   Let the market satisfy the standing assumptions. Then the explicit bound $\bar r = \min\{2, \bar r_0, \bar r_1\}$ of (G.2)–(G.4) is strictly positive, and for every $r \in (0, \bar r)$, under the inertial policy with $\rho(z) = 1/(r_0 + rz)$:
--
--   1. (T3:1) For every hypothesis $i \in \{0,1\}$ and every $z \in \mathbb Z$, $J^i(z) < +\infty$, where $J^i(z)$ is the supremum over admissible strategies of the liminf of the informed bettor's total expected profit from state $z$.
--   2. (T3:2) The threshold $\bar z$ of (G.1) lies in $\mathbb Z \cup \{-\infty\}$, and for each $i$ the threshold strategy
--   $$
--   \xi_1^*(z) = \mathbb I\{z < \bar z\},\qquad \xi_0^*(z) = -\mathbb I\{z > -\bar z\} \tag{4.4}
--   $$
--   is a best response in the sense of (2.3), against all admissible (history-dependent, randomized) strategies.
--
--   Under the inertial policy the informed bettor therefore earns a bounded profit and bets honestly; he has no incentive to bluff.
--
--   **Formalization Note** The paper's "there exists $\bar r > 0$ … given in Appendix G.2" is stated with the explicit $\bar r$ of (G.2) and its positivity (Remark 1, p. 49). "$\bar z \in \mathbb Z \cup\{-\infty\}$" is the nonemptiness of the set in (G.1).
-- source:
--   Birge, Feng, Keskin & Schultz, SSRN 3283392 (version of April 14, 2020), p. 17, Theorem 3, (4.4); (2.3) p. 9; (G.1)–(G.4) and Remark 1, p. 49

import Mathlib
import Definitions.Def_SpreadBetting_Inertial_Model

namespace SpreadBetting.Inertial

open MeasureTheory ProbabilityTheory Filter Topology

theorem theorem_3 (M : Market) (hM : M.Standing) :
    0 < rbar M ∧
    ∀ r : ℝ, 0 < r → r < rbar M →
      let ρp := rhoIP M r
      -- (T3:1)
      (∀ (i : Fin 2) (z : ℤ), Jval M ρp i z < ⊤) ∧
      -- (T3:2): z̄ ∈ ℤ ∪ {-∞} and the threshold strategy (4.4) is a best response (2.3)
      (zbarSet M ρp).Nonempty ∧ ∀ i : Fin 2, IsBestResponse M ρp i (xiStar M ρp i) := by sorry

end SpreadBetting.Inertial
