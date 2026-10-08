-- Prove2me | Theorems.Thm_WardropTraffic_MinTime_unused_of_marginal_ge
-- name    : WardropTraffic.MinTime.unused_of_marginal_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:52:48.534186+00:00
-- url     : https://prove2.me/theorems/6fc8ead2-266f-4563-98d9-f0502c70fa56
-- title:
--   p. 346 — a route j with zero-flow marginal time bⱼ ≥ ε is not used
-- statement:
--   In the setting of the minimum-average-time problem ($b_i, p_i > 0$, $0 < Q < \sum_i p_i$), let $q$ minimize the average journey time $T$ over the feasible splits of $Q$, and let $\varepsilon$ be a common marginal time of the routes in use, i.e. $b_i/(1 - q_i/p_i)^2 = \varepsilon$ whenever $q_i > 0$. Then for every route $j$,
--   $$
--   \left[\frac{d(q_j t_j)}{dq_j}\right]_{q=0} = b_j \ \ge\ \varepsilon \quad\Longrightarrow\quad q_j = 0 .
--   $$
--   This is the paper's rule that a route whose marginal time at zero flow is at least the common marginal time $\varepsilon$ attracts no flow at the optimum.
--
--   **Formalization Note** The zero-flow marginal time is written as $b_j$, its value by (30). The standing conditions are those of the model.
-- source:
--   Wardrop, Some theoretical aspects of road traffic research, Proc. Instn Civ. Engrs Part II 1 (1952), p. 346, the sentence following (28)

import Mathlib
import Definitions.Def_WardropTraffic_MinTime_Setting

namespace WardropTraffic.MinTime

/-- p. 346: if `ε` is the common marginal time of the routes in use at a minimum, a route
whose zero-flow marginal time `b_j` is at least `ε` is not used. -/
theorem unused_of_marginal_ge {D : ℕ} (b p : Fin D → ℝ) (Q : ℝ)
    (hb : ∀ i, 0 < b i) (hp : ∀ i, 0 < p i) (hQ : 0 < Q) (hQp : Q < ∑ i, p i)
    (q : Fin D → ℝ) (hmin : IsMinAvgTime b p Q q) (ε : ℝ)
    (hε : ∀ i, 0 < q i → b i / (1 - q i / p i) ^ 2 = ε) :
    ∀ j, ε ≤ b j → q j = 0 := by sorry

end WardropTraffic.MinTime
