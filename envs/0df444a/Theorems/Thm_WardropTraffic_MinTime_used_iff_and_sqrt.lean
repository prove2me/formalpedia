-- Prove2me | Theorems.Thm_WardropTraffic_MinTime_used_iff_and_sqrt
-- name    : WardropTraffic.MinTime.used_iff_and_sqrt
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:53:26.544464+00:00
-- url     : https://prove2.me/theorems/2837159b-fe6e-46e2-b16c-bfa289ffb7a0
-- title:
--   p. 346 — the routes in use are exactly those with bᵢ < ε, and on them 1 − qᵢ/pᵢ = √(bᵢ/ε)
-- statement:
--   In the setting of the minimum-average-time problem ($b_i, p_i > 0$, $0 < Q < \sum_i p_i$), let $q$ minimize the average journey time $T$ over the feasible splits of $Q$, and let $\varepsilon$ be a common marginal time of the routes in use: $b_i/(1 - q_i/p_i)^2 = \varepsilon$ whenever $q_i > 0$. Then $\varepsilon > 0$ and for every route $i$:
--
--   1. route $i$ is used if and only if $b_i < \varepsilon$;
--   2. if route $i$ is used, then
--   $$
--   1 - \frac{q_i}{p_i} = \sqrt{\frac{b_i}{\varepsilon}}, \qquad\text{equivalently}\qquad p_i - q_i = p_i \sqrt{\frac{b_i}{\varepsilon}} .
--   $$
--
--   With the routes labelled so that $b_1 < b_2 < \dots < b_D$, part 1 is the paper's "if $b_j < \varepsilon < b_{j+1}$ only the first $j$ routes will be in use", and part 2 solves (28) for the flows.
--
--   **Formalization Note** The ordering of the $b_i$ is not assumed: "the first $j$ routes" is the set $\{i : b_i < \varepsilon\}$. The standing conditions are those of the model.
-- source:
--   Wardrop, Some theoretical aspects of road traffic research, Proc. Instn Civ. Engrs Part II 1 (1952), p. 346, after (30): 'Thus if b_j < ε < b_{j+1} only the first j routes will be in use. Hence 1 − q_i/p_i = √(b_i/ε) and so p_i − q_i = p_i√(b_i/ε)'

import Mathlib
import Definitions.Def_WardropTraffic_MinTime_Setting

namespace WardropTraffic.MinTime

/-- p. 346: at a minimum with common marginal time `ε`, `ε > 0`, the routes in use are
exactly those with `b_i < ε`, and on each of them `1 - q_i/p_i = √(b_i/ε)`. -/
theorem used_iff_and_sqrt {D : ℕ} (b p : Fin D → ℝ) (Q : ℝ)
    (hb : ∀ i, 0 < b i) (hp : ∀ i, 0 < p i) (hQ : 0 < Q) (hQp : Q < ∑ i, p i)
    (q : Fin D → ℝ) (hmin : IsMinAvgTime b p Q q) (ε : ℝ)
    (hε : ∀ i, 0 < q i → b i / (1 - q i / p i) ^ 2 = ε) :
    0 < ε ∧ ∀ i, (0 < q i ↔ b i < ε) ∧
      (0 < q i → 1 - q i / p i = Real.sqrt (b i / ε)) := by sorry

end WardropTraffic.MinTime
