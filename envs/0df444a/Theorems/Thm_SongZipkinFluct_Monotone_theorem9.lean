-- Prove2me | Theorems.Thm_SongZipkinFluct_Monotone_theorem9
-- name    : SongZipkinFluct.Monotone.theorem9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:40:45.594324+00:00
-- url     : https://prove2.me/theorems/ef421562-4072-48dc-86fc-af42ba07f098
-- title:
--   Theorem 9 — if the world never moves down in ⪯, the myopic policy is optimal: y*(i) = y⁺(i)
-- statement:
--   Assume the standing hypotheses of the model, Assumption 1 and Condition 1 for a partial order $\preceq$ on the world states, and suppose that for each fixed $i$, $q_{ij} \ne 0$ only if $j \succeq i$. In the linear-cost model ($K = 0$, $W_0 \equiv 0$) the smallest minimizers $y^+(i)$ of $G^+(i,\cdot)$ and $y^*(i)$ of $G_\infty(i,\cdot)$ exist, and
--   $$y^*(i) = y^+(i) \quad \text{for all } i.$$
--
--   In the paper's words, the myopic policy $\pi(y^+)$ (Definition 1) is then optimal: when the demand rate, while fluctuating, never decreases, the basestock level that minimizes the one-step cost is already optimal. This is the continuous-time analogue of Veinott's (1965) result for nondecreasing demand.
--
--   **Formalization Note.** The conclusion is the paper's own gloss "$y^*(i) = y^+(i)$". Optimality of the policy $\pi(y^*)$ is Theorem 2(e) of the paper and is not restated here. The hypothesis on $Q$ is taken literally, for all $j$ including $j = i$.
-- source:
--   Song and Zipkin, Inventory Control in a Fluctuating Demand Environment, Oper. Res. 41(2):351–370 (1993), DOI 10.1287/opre.41.2.351, p. 360, §4.2, Theorem 9

import Mathlib
import Definitions.Def_SongZipkinFluct_Monotone_Condition1
import Definitions.Def_SongZipkinFluct_Monotone_Recursion

namespace SongZipkinFluct.Monotone

/-- **Theorem 9** (Song and Zipkin 1993, §4.2, p. 360): "Suppose that condition 1 holds and for each
fixed `i`, `q_ij ≠ 0` only if `j ⪰ i`. Then the myopic policy is optimal, that is, `y*(i) = y⁺(i)`
for all `i`."

**Formalization Note.** The conclusion is the paper's own gloss, `y*(i) = y⁺(i)` (smallest
minimizers of `G_∞(i, ·)` and `G⁺(i, ·)`, linear-cost model `K = 0`, `W₀ ≡ 0`), stated with the
existence of both. That the myopic policy `π(y⁺)` (Definition 1, p. 356) is then optimal follows
from Theorem 2(e), p. 358, which is not restated here. -/
theorem theorem9 {I : Type} [Countable I] [Nonempty I] [DecidableEq I] [PartialOrder I]
    (M : Model I) (hM : M.Standing) (hA : M.Assumption1) (hC : M.Condition1)
    (hQ : ∀ i j : I, M.Q i j ≠ 0 → i ≤ j) :
    (∃ yplus : I → ℤ, ∀ i, IsSmallestMinimizer (M.Gplus i) (yplus i)) ∧
    (∃ ystar : I → ℤ, ∀ i, IsSmallestMinimizer (M.Ginf 0 0 i) (ystar i)) ∧
    ∀ yplus ystar : I → ℤ,
      (∀ i, IsSmallestMinimizer (M.Gplus i) (yplus i)) →
      (∀ i, IsSmallestMinimizer (M.Ginf 0 0 i) (ystar i)) →
      ∀ i, ystar i = yplus i := by sorry

end SongZipkinFluct.Monotone
