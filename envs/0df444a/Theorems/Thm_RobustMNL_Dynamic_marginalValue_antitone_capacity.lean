-- Prove2me | Theorems.Thm_RobustMNL_Dynamic_marginalValue_antitone_capacity
-- name    : RobustMNL.Dynamic.marginalValue_antitone_capacity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:23:09.956791+00:00
-- url     : https://prove2.me/theorems/b19b7565-f661-4b90-b4a5-9c0e5bd87cae
-- title:
--   Theorem 4.1, p. 16, first inequality — ΔJ_t(x + 1) ≤ ΔJ_t(x): the value function is concave in capacity
-- statement:
--   In the robust capacity-allocation model, for every period $1 \le t \le T$ and every capacity level $x \ge 1$,
--   $$\Delta J_t(x+1) \le \Delta J_t(x),$$
--   where $\Delta J_t(x) = J_t(x) - J_t(x-1)$ is the marginal value of capacity. Equivalently, $x \mapsto J_t(x)$ is concave on $\mathbb N$.
--
--   Concavity in capacity is the first half of Theorem 4.1, and gives the nonnegative increment $\Delta J_{t+1}(x) - \Delta J_{t+1}(x+1)$ used in Theorem 4.3.
--
--   **Formalization Note** The paper states the theorem "for any $x \in \{0, 1, \dots, C\}$"; at $x = 0$ the term $\Delta J_t(0) = J_t(0) - J_t(-1)$ is undefined, so the statement is made for $x \ge 1$. $J$ is defined for all $x \in \mathbb N$ (the recursion does not use $C$), so the statement for all $x \ge 1$ contains the paper's for every $C$. Revenues are arbitrary reals.
-- source:
--   Rusmevichientong, Topaloglu, Robust Assortment Optimization in Revenue Management Under the Multinomial Logit Choice Model, Operations Research (2012), doi:10.1287/opre.1120.1063, authors' manuscript of 20 Sep 2011, Theorem 4.1 (first inequality), p. 16; proof in Appendix A, pp. 30–32

import Mathlib
import Definitions.Def_RobustMNL_Dynamic_ValueFunction

namespace RobustMNL.Dynamic

theorem marginalValue_antitone_capacity {n : ℕ} (T : ℕ) (V : ℕ → Set (ℝ × (Fin n → ℝ)))
    (r : Fin n → ℝ) (hV : IsUncertaintySeq T V) (t x : ℕ) (ht : 1 ≤ t) (htT : t ≤ T) (hx : 1 ≤ x) :
    marginalValue T V r t (x + 1) ≤ marginalValue T V r t x := by sorry

end RobustMNL.Dynamic
