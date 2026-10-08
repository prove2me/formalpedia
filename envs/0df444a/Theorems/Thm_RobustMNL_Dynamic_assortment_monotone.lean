-- Prove2me | Theorems.Thm_RobustMNL_Dynamic_assortment_monotone
-- name    : RobustMNL.Dynamic.assortment_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:23:13.815976+00:00
-- url     : https://prove2.me/theorems/0a514d5c-bc89-42bb-8d51-bb6f74fe28f4
-- title:
--   Theorem 4.3, p. 17 — S*_t(x) ⊆ S*_t(x + 1), and S*_t(x) ⊆ S*_{t+1}(x) when V_t ⊆ V_{t+1}
-- statement:
--   In the robust capacity-allocation model over periods $1, \dots, T$, with compact nonempty uncertainty sets $\mathcal V_t \subseteq \mathbb R^{n+1}_{++}$, let $S^*_t(x)$ denote an optimal assortment of smallest cardinality of the period-$t$ Bellman problem with capacity $x$. Then:
--
--   1. For every $1 \le t \le T$ and $x \ge 1$,
--   $$S^*_t(x) \subseteq S^*_t(x+1).$$
--   2. For every $1 \le t \le T-1$ and $x \ge 1$ with $\mathcal V_t \subseteq \mathcal V_{t+1}$,
--   $$S^*_t(x) \subseteq S^*_{t+1}(x).$$
--
--   More remaining capacity leads to a larger optimal assortment; and, when uncertainty does not shrink over time, so does approaching the end of the horizon. This is the robust analogue of the nesting properties of single-leg revenue management.
--
--   **Formalization Note** Each part holds for every pair of smallest-cardinality maximizers (`IsOptAssort`). "For any $x$" is read as $x \ge 1$ ($S^*_t(0)$ is not defined by the Bellman equation); "for any $t$" is $1 \le t \le T$, and $t + 1 \le T$ in part 2 so that $S^*_{t+1}(x)$ exists. The only hypothesis of part 2 beyond the standing assumptions is $\mathcal V_t \subseteq \mathcal V_{t+1}$. $J$ is defined for every $x \in \mathbb N$, so no capacity bound $C$ appears. Revenues are arbitrary reals (the paper's $r_1 \ge \dots \ge r_n > 0$ is dropped).
-- source:
--   Rusmevichientong, Topaloglu, Robust Assortment Optimization in Revenue Management Under the Multinomial Logit Choice Model, Operations Research (2012), doi:10.1287/opre.1120.1063, authors' manuscript of 20 Sep 2011, Theorem 4.3, p. 17; proof pp. 17–18

import Mathlib
import Definitions.Def_RobustMNL_Dynamic_ValueFunction

namespace RobustMNL.Dynamic

theorem assortment_monotone {n : ℕ} (T : ℕ) (V : ℕ → Set (ℝ × (Fin n → ℝ)))
    (r : Fin n → ℝ) (hV : IsUncertaintySeq T V) :
    (∀ (t x : ℕ) (S S' : Finset (Fin n)), 1 ≤ t → t ≤ T → 1 ≤ x →
        IsOptAssort T V r t x S → IsOptAssort T V r t (x + 1) S' → S ⊆ S') ∧
      (∀ (t x : ℕ) (S S' : Finset (Fin n)), 1 ≤ t → t + 1 ≤ T → 1 ≤ x → V t ⊆ V (t + 1) →
        IsOptAssort T V r t x S → IsOptAssort T V r (t + 1) x S' → S ⊆ S') := by sorry

end RobustMNL.Dynamic
