-- Prove2me | Theorems.Thm_WardropTraffic_EqualTimes_used_imp_lt
-- name    : WardropTraffic.EqualTimes.used_imp_lt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:53:01.177971+00:00
-- url     : https://prove2.me/theorems/1e68e6cd-48fe-4754-a4a0-7a333de4cf6d
-- title:
--   p. 345 — under equal times t, only routes with bᵢ < t are in use
-- statement:
--   Consider $D$ routes with positive constants $b_i, p_i$ and journey times $t_i(x) = b_i/(1 - x/p_i)$. Let $q$ be a feasible split of the flow $Q$ ($0 \le q_i < p_i$, $\sum_i q_i = Q$) satisfying the equal-times criterion (1) with common time $t$: $t_i(q_i) = t$ whenever $q_i > 0$, and $t \le b_i$ whenever $q_i = 0$. Then for every route $i$,
--   $$
--   q_i > 0 \implies b_i < t .
--   $$
--   In the paper's labelling $b_1 < \dots < b_D$ with $b_j < t \le b_{j+1}$, only the first $j$ routes can be in use.
--
--   **Formalization Note** "The first $j$ routes" is expressed as the set of routes with $b_i < t$; the ordering of the $b_i$ is not assumed. The criterion's comparison on unused routes is the weak $t \le b_i$ (see the definitions file).
-- source:
--   Wardrop, Some theoretical aspects of road traffic research, Proc. Instn Civ. Engrs Part II 1 (1952), p. 345, (1) Equal Times: "Then clearly only the first j routes can be in use"

import Mathlib
import Definitions.Def_WardropTraffic_EqualTimes_Setting

namespace WardropTraffic.EqualTimes

theorem used_imp_lt {D : ℕ} (b p : Fin D → ℝ) (hb : ∀ i, 0 < b i) (hp : ∀ i, 0 < p i)
    (Q t : ℝ) (q : Fin D → ℝ) (h : IsEqualTimes b p Q q t) :
    ∀ i, 0 < q i → b i < t := by sorry

end WardropTraffic.EqualTimes
