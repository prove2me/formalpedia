-- Prove2me | Theorems.Thm_RobustMNL_Dynamic_revenue_ordered_optimal
-- name    : RobustMNL.Dynamic.revenue_ordered_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:22:14.723869+00:00
-- url     : https://prove2.me/theorems/39d3dac1-588b-4982-a699-c30ac360cebb
-- title:
--   Theorem 4.2, p. 16 — revenue-ordered assortments are optimal: S*_t(x) = {i : rᵢ > J_t(x) − J_{t+1}(x − 1)}
-- statement:
--   In the robust capacity-allocation model, let $1 \le t \le T$ and $x \ge 1$. An assortment $S$ is $S^*_t(x)$, an optimal assortment of smallest cardinality of the period-$t$ Bellman problem with capacity $x$, if and only if
--   $$S = \{\, i \in \mathcal A : r_i > J_t(x) - J_{t+1}(x-1) \,\}.$$
--
--   The optimal dynamic assortment consists of the products whose revenue exceeds the opportunity cost $J_t(x) - J_{t+1}(x-1)$ of selling a unit now; in particular it is revenue-ordered, extending the known-parameter result of Talluri and van Ryzin (2004).
--
--   **Formalization Note** "For any $x$" is read as $x \ge 1$: at $x = 0$ the Bellman equation does not apply ($J_t(0) = 0$ is a boundary condition) and $J_{t+1}(x-1)$ is undefined. The "↔" asserts both that every smallest optimal assortment is the threshold set and that the threshold set is one. Revenues are arbitrary reals.
-- source:
--   Rusmevichientong, Topaloglu, Robust Assortment Optimization in Revenue Management Under the Multinomial Logit Choice Model, Operations Research (2012), doi:10.1287/opre.1120.1063, authors' manuscript of 20 Sep 2011, Theorem 4.2, p. 16

import Mathlib
import Definitions.Def_RobustMNL_Dynamic_ValueFunction

namespace RobustMNL.Dynamic

theorem revenue_ordered_optimal {n : ℕ} (T : ℕ) (V : ℕ → Set (ℝ × (Fin n → ℝ)))
    (r : Fin n → ℝ) (hV : IsUncertaintySeq T V) (t x : ℕ) (ht : 1 ≤ t) (htT : t ≤ T) (hx : 1 ≤ x)
    (S : Finset (Fin n)) :
    IsOptAssort T V r t x S ↔
      S = Finset.univ.filter (fun i => J T V r t x - J T V r (t + 1) (x - 1) < r i) := by sorry

end RobustMNL.Dynamic
