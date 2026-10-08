-- Prove2me | Theorems.Thm_WardropTraffic_MinTime_min_average_time_closed_form
-- name    : WardropTraffic.MinTime.min_average_time_closed_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:52:56.701645+00:00
-- url     : https://prove2.me/theorems/d9ae1067-7405-4292-8756-8adb47a79b47
-- title:
--   (32)–(33), p. 347 — the minimum average journey time and its flows in closed form ((33) with denominator Σpᵢ√bᵢ)
-- statement:
--   A flow $Q$ is split over $D$ alternative routes, route $i$ having journey time $t_i(x) = b_i/(1 - x/p_i)$ at additional flow $x$ (equation (22)), with constants $b_i > 0$, $p_i > 0$, and $0 < Q < \sum_{i=1}^D p_i$. A feasible split is $q = (q_1, \dots, q_D)$ with $0 \le q_i < p_i$ and $\sum_i q_i = Q$, and its average journey time is $T(q) = \frac1Q\sum_i q_i t_i(q_i)$ (equation (25)).
--
--   If $q$ minimizes $T$ over all feasible splits, then there is a threshold $\varepsilon > 0$ such that, with $U = \{i : b_i < \varepsilon\}$ the set of routes in use, $\sum_{i \in U} p_i > Q$ and:
--
--   1. the flows are (33)
--   $$
--   q_h = \begin{cases} p_h\left\{1 - \dfrac{\left(\sum_{i\in U} p_i - Q\right)\sqrt{b_h}}{\sum_{i\in U} p_i\sqrt{b_i}}\right\}, & b_h < \varepsilon,\\[2ex] 0, & b_h \ge \varepsilon; \end{cases}
--   $$
--   2. the minimum average journey time is (32)
--   $$
--   T = \frac{1}{Q}\left\{\frac{\left(\sum_{i \in U} p_i\sqrt{b_i}\right)^2}{\sum_{i\in U} p_i - Q} - \sum_{i\in U} p_i b_i\right\}.
--   $$
--
--   With the routes labelled so that $b_1 < \dots < b_D$, $U$ is "the first $j$ routes" of the paper. This is the paper's solution of the system-optimal assignment problem on parallel routes, to be compared with the equal-times solution (23)–(24) of the same model.
--
--   **Formalization Note** The paper prints the denominator in (33) as $\sum_{i=1}^{j} p_i b_i$. That is a slip: from (31), $1/\sqrt{\varepsilon} = (\sum p_i - Q)/\sum p_i\sqrt{b_i}$, so $q_h = p_h(1 - \sqrt{b_h/\varepsilon})$ gives the denominator $\sum p_i\sqrt{b_i}$ stated here; the printed form is also not dimensionless, since $b_i$ is a time. With $b = (4, 9)$, $p = (10, 10)$, $Q = 35/3$ the minimizing flow is $q_1 = 20/3$, which the corrected formula returns and the printed one does not. Equation (32) is correct as printed. The conditions $b_i, p_i > 0$, $0 < Q < \sum_i p_i$ and $q_i < p_i$ are the model's standing conditions (positive speeds, a nontrivial flow, a nonempty feasible set). No ordering of the $b_i$ is assumed. The threshold $\varepsilon$ is existential; a route with $b_h = \varepsilon$ carries no flow by either branch.
-- source:
--   Wardrop, Some theoretical aspects of road traffic research, Proc. Instn Civ. Engrs Part II 1 (1952), p. 347, (32)–(33) (denominator of (33) corrected from Σpᵢbᵢ to Σpᵢ√bᵢ)

import Mathlib
import Definitions.Def_WardropTraffic_MinTime_Setting

namespace WardropTraffic.MinTime

/-- (32)–(33), with the denominator of (33) corrected to `∑ p_i √b_i`: every split
minimizing the average journey time has a threshold `ε > 0` such that exactly the routes
with `b_h < ε` are used, with the flows (33) and the minimum average time (32). -/
theorem min_average_time_closed_form {D : ℕ} (b p : Fin D → ℝ) (Q : ℝ)
    (hb : ∀ i, 0 < b i) (hp : ∀ i, 0 < p i) (hQ : 0 < Q) (hQp : Q < ∑ i, p i)
    (q : Fin D → ℝ) (hmin : IsMinAvgTime b p Q q) :
    ∃ ε : ℝ, 0 < ε ∧ Q < ∑ i ∈ WardropTraffic.EqualTimes.usedSet b ε, p i ∧
      (∀ h, q h = if b h < ε then
          p h * (1 - (∑ i ∈ WardropTraffic.EqualTimes.usedSet b ε, p i - Q) * Real.sqrt (b h) /
            ∑ i ∈ WardropTraffic.EqualTimes.usedSet b ε, p i * Real.sqrt (b i))
        else 0) ∧
      avgTime b p Q q = (1 / Q) * ((∑ i ∈ WardropTraffic.EqualTimes.usedSet b ε, p i * Real.sqrt (b i)) ^ 2 /
          (∑ i ∈ WardropTraffic.EqualTimes.usedSet b ε, p i - Q) - ∑ i ∈ WardropTraffic.EqualTimes.usedSet b ε, p i * b i) := by sorry

end WardropTraffic.MinTime
