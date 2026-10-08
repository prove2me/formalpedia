-- Prove2me | Theorems.Thm_WardropTraffic_MinTime_marginal_times_equal
-- name    : WardropTraffic.MinTime.marginal_times_equal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:52:57.387085+00:00
-- url     : https://prove2.me/theorems/d10789f3-0d1f-42f1-9179-49ee8442463d
-- title:
--   (27)–(28), p. 346 — at a minimum of T, all routes in use have the same marginal time ε
-- statement:
--   Let $b_1, \dots, b_D > 0$ and $p_1, \dots, p_D > 0$ describe $D$ alternative routes with journey times $t_i(x) = b_i/(1 - x/p_i)$, and let $0 < Q < \sum_i p_i$. Suppose the feasible split $q$ of $Q$ minimizes the average journey time $T$ (criterion (2)). Then there is a constant $\varepsilon$, independent of the route, with
--   $$
--   \frac{b_i}{(1 - q_i/p_i)^2} = \varepsilon \qquad \text{for every route } i \text{ with } q_i > 0 .
--   $$
--   By (29) the left side is the marginal time $d(q_i t_i)/dq_i$, so this is (27)–(28): moving an infinitesimal amount of flow between two routes in use must not change $Z$. It is the system-optimum counterpart of the equal-times principle.
--
--   **Formalization Note** The marginal time is written in its closed form (29) rather than as a derivative. The conditions $b_i, p_i > 0$ and $0 < Q < \sum_i p_i$ are the model's standing conditions: positive speeds, a nontrivial flow, and a nonempty feasible set.
-- source:
--   Wardrop, Some theoretical aspects of road traffic research, Proc. Instn Civ. Engrs Part II 1 (1952), p. 346, (27)–(28)

import Mathlib
import Definitions.Def_WardropTraffic_MinTime_Setting

namespace WardropTraffic.MinTime

/-- (27)–(28): at a minimum of the average journey time, the marginal journey times
`b_i / (1 - q_i/p_i)^2` of all routes in use equal one constant `ε`. -/
theorem marginal_times_equal {D : ℕ} (b p : Fin D → ℝ) (Q : ℝ)
    (hb : ∀ i, 0 < b i) (hp : ∀ i, 0 < p i) (hQ : 0 < Q) (hQp : Q < ∑ i, p i)
    (q : Fin D → ℝ) (hmin : IsMinAvgTime b p Q q) :
    ∃ ε : ℝ, ∀ i, 0 < q i → b i / (1 - q i / p i) ^ 2 = ε := by sorry

end WardropTraffic.MinTime
