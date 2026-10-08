-- Prove2me | Theorems.Thm_WardropTraffic_MinTime_sum_eq_sqrt
-- name    : WardropTraffic.MinTime.sum_eq_sqrt
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:52:47.296335+00:00
-- url     : https://prove2.me/theorems/377f77f1-94e2-4da1-97ac-7ba8d6cb558b
-- title:
--   (31), p. 346 — Σ_{bᵢ<ε} pᵢ − Q = Σ_{bᵢ<ε} pᵢ√(bᵢ/ε)
-- statement:
--   In the setting of the minimum-average-time problem ($b_i, p_i > 0$, $0 < Q < \sum_i p_i$), let $q$ minimize the average journey time $T$ over the feasible splits of $Q$, and let $\varepsilon$ be a common marginal time of the routes in use: $b_i/(1 - q_i/p_i)^2 = \varepsilon$ whenever $q_i > 0$. Write $U(\varepsilon) = \{i : b_i < \varepsilon\}$ for the set of routes in use. Then
--   $$
--   \sum_{i \in U(\varepsilon)} p_i - Q = \sum_{i \in U(\varepsilon)} p_i \sqrt{\frac{b_i}{\varepsilon}} .
--   $$
--   This is equation (31), obtained on the page by summing $p_i - q_i = p_i\sqrt{b_i/\varepsilon}$ over the routes in use. It determines $\varepsilon$ from $Q$, and leads to the closed forms (32)–(33).
--
--   **Formalization Note** The paper's sum over "the first $j$ routes" is the sum over $U(\varepsilon)$; no ordering of the $b_i$ is assumed. The standing conditions are those of the model.
-- source:
--   Wardrop, Some theoretical aspects of road traffic research, Proc. Instn Civ. Engrs Part II 1 (1952), p. 346, (31)

import Mathlib
import Definitions.Def_WardropTraffic_MinTime_Setting

namespace WardropTraffic.MinTime

/-- (31): summing `p_i - q_i = p_i √(b_i/ε)` over the routes in use,
`∑_{b_i < ε} p_i - Q = ∑_{b_i < ε} p_i √(b_i/ε)`. -/
theorem sum_eq_sqrt {D : ℕ} (b p : Fin D → ℝ) (Q : ℝ)
    (hb : ∀ i, 0 < b i) (hp : ∀ i, 0 < p i) (hQ : 0 < Q) (hQp : Q < ∑ i, p i)
    (q : Fin D → ℝ) (hmin : IsMinAvgTime b p Q q) (ε : ℝ)
    (hε : ∀ i, 0 < q i → b i / (1 - q i / p i) ^ 2 = ε) :
    ∑ i ∈ WardropTraffic.EqualTimes.usedSet b ε, p i - Q = ∑ i ∈ WardropTraffic.EqualTimes.usedSet b ε, p i * Real.sqrt (b i / ε) := by sorry

end WardropTraffic.MinTime
