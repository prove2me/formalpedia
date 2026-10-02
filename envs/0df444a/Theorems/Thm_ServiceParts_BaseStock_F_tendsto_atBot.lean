-- Prove2me | Theorems.Thm_ServiceParts_BaseStock_F_tendsto_atBot
-- name    : ServiceParts.BaseStock.F_tendsto_atBot
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T21:32:17.21525+00:00
-- url     : https://prove2.me/theorems/a3cf359a-351b-4c63-9eaa-24b9917feb6a
-- title:
--   Limit of $F_n(w)$ as $w \to -\infty$ equals $(1-\alpha)c - b\alpha < 0$
-- statement:
--   In the model of Section 2.1 with lead time one period, let $n \ge 2$ and suppose the order-up-to rule with a real level $s$ is optimal in the $n$-period problem. Then
--   $$
--   F_n(w) = c + \alpha\int_0^\infty f_n'(w-x)\,g(x)\,dx \;\longrightarrow\; (1-\alpha)c - b\alpha \qquad (w \to -\infty),
--   $$
--   and this limit is negative.
--
--   Negativity of $F_n$ far to the left, together with its positivity far to the right, is what produces a finite root $s_{n+1}^*$ of $F_n$, the next order-up-to level.
--
--   **Formalization Note** The hypothesis that a real level $s$ exists for horizon $n$ is essential: for $n = 1$ ($f_1 = L$, no order) the limit is $c - b\alpha$ instead, which the book's assumption $b > \frac{1-\alpha}{\alpha}c$ does not make negative.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 19, Section 2.1, proof of Theorem 2

import Mathlib
import Definitions.Def_ServiceParts_BaseStock_Model
import Definitions.Def_ServiceParts_BaseStock_Recursion

open MeasureTheory Set Filter Topology

namespace ServiceParts.BaseStock

/-- Section 2.1, p. 19: if the order-up-to rule with a (finite) level s is optimal in the
n-period problem (n ≥ 2), then as w → −∞,
Fₙ(w) = c + α ∫₀^∞ f′ₙ(w − x) g(x) dx → (1 − α)c − bα, and this limit is negative. -/
theorem F_tendsto_atBot (M : Model) (n : ℕ) (hn : 2 ≤ n) (s : ℝ)
    (hs : M.IsOrderUpToOptimal n s) :
    Tendsto (M.F n) atBot (𝓝 ((1 - M.α) * M.c - M.b * M.α)) ∧
      (1 - M.α) * M.c - M.b * M.α < 0 := by sorry

end ServiceParts.BaseStock
