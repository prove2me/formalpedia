-- Prove2me | Theorems.Thm_WardropTraffic_EqualTimes_equal_times_characterization
-- name    : WardropTraffic.EqualTimes.equal_times_characterization
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:53:35.081665+00:00
-- url     : https://prove2.me/theorems/892a7ed2-7b6c-474a-8753-bedd6b361674
-- title:
--   (23)–(24), p. 345 — under equal times t, exactly the routes with bᵢ < t are used, qᵢ = pᵢ(1 − bᵢ/t), Q = Σpᵢ − t⁻¹Σpᵢbᵢ
-- statement:
--   Consider a flow $Q$ that chooses among $D$ alternative routes. Route $i$ has positive constants $b_i$ (empty-route journey time) and $p_i$, and carries journey time $t_i(x) = b_i/(1 - x/p_i)$ at additional flow $x$ (equation (22)). Write $U(t) = \{ i : b_i < t \}$.
--
--   For every $Q, t \in \mathbb R$ and every flow vector $q = (q_1, \dots, q_D)$, the following are equivalent:
--
--   1. $q$ is a feasible split of $Q$ ($0 \le q_i < p_i$, $\sum_i q_i = Q$) satisfying the equal-times criterion (1) with common time $t$: every used route has $t_i(q_i) = t$ and every unused route has $t \le b_i$;
--   2. the flows and the total are given by (23) and (24):
--   $$
--   q_i = \begin{cases} p_i\bigl(1 - b_i/t\bigr) & \text{if } b_i < t,\\ 0 & \text{otherwise,}\end{cases}
--   \qquad
--   Q = \sum_{i \in U(t)} p_i - \frac{1}{t} \sum_{i \in U(t)} p_i b_i .
--   $$
--
--   The forward direction is Wardrop's derivation: exactly the routes faster than $t$ when empty are used, each carries the flow (23), and summing gives (24), the value of $Q$ for which $t$ is the appropriate journey time. The backward direction says that (23)–(24) are indeed an equal-times split, which is what makes it possible to solve the problem by picking the $t$ corresponding to the given $Q$.
--
--   **Formalization Note** The paper's labelling $b_1 < \dots < b_D$ and "the first $j$ routes" are replaced by the set $U(t)$, a generalisation that also covers ties. The criterion on unused routes is the weak $t \le b_i$, which the paper's case split $b_j < t \not> b_{j+1}$ uses; every split satisfying the printed strict criterion satisfies it. No sign condition on $t$ or $Q$ is assumed: for $t \le \min_i b_i$ both sides force $q = 0$ and $Q = 0$ (the term $1/t$ then multiplies an empty sum).
-- source:
--   Wardrop, Some theoretical aspects of road traffic research, Proc. Instn Civ. Engrs Part II 1 (1952), p. 345, (1) Equal Times, (23)–(24)

import Mathlib
import Definitions.Def_WardropTraffic_EqualTimes_Setting

namespace WardropTraffic.EqualTimes

theorem equal_times_characterization {D : ℕ} (b p : Fin D → ℝ) (hb : ∀ i, 0 < b i)
    (hp : ∀ i, 0 < p i) (Q t : ℝ) (q : Fin D → ℝ) :
    IsEqualTimes b p Q q t ↔
      ((∀ i, q i = if b i < t then p i * (1 - b i / t) else 0) ∧
        Q = ∑ i ∈ usedSet b t, p i - (1 / t) * ∑ i ∈ usedSet b t, p i * b i) := by sorry

end WardropTraffic.EqualTimes
